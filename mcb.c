/* ---------------------------------------------------------------------------
 * mcb  -- simple memcached benchmark 
 * version: 1.0
 * author: suzuki hironobu (hironobu@interdb.jp) 2008.Jun.25     0.9
 * author: suzuki hironobu (hironobu@interdb.jp) 2009.Nov.4      1.0RC1
 * author: suzuki hironobu (hironobu@interdb.jp) 2009.Dec.15     1.0RC2
 * author: suzuki hironobu (hironobu@interdb.jp) 2010.Dec.7      1.0RC3
 * author: suzuki hironobu (hironobu@interdb.jp) 2011.Feb.9      1.0RC4
 * author: suzuki hironobu (hironobu@interdb.jp) 2011.Mar.1      1.0RC5
 * author: suzuki hironobu (hironobu@interdb.jp) 2014.Jul.1      1.0
 *       Tested by using CBMC(http://www.cprover.org/cbmc/),
 *                       valgrind(http://valgrind.org/),
 *                       and Intel Inspector XE.
 *
 * Copyright (C) 2008-2014  suzuki hironobu
 *
 * ---------------------------------------------------------------------------
 */

#include <stdio.h>
#include <stdlib.h>
#include <strings.h>
#include <ctype.h>
#include <pthread.h>
#include <sys/un.h>
#include <arpa/inet.h>
#include <sys/time.h>
#include <unistd.h>
#include <assert.h>

#ifndef C_H
#ifndef bool
typedef char bool;
#endif
#ifndef true
#define true    ((bool) 1)
#endif
#ifndef false
#define false   ((bool) 0)
#endif
typedef bool *BoolPtr;
#ifndef TRUE
#define TRUE    1
#endif
#ifndef FALSE
#define FALSE   0
#endif
#ifndef NULL
#define NULL    ((void *) 0)
#endif
#endif

#ifdef __CBMC__
#define elog(_message_) fprintf(stderr, "%s\n", _message_);
#else
#define elog(_message_)  do {fprintf(stderr, \
				     "%s():%s:%u: %s\n",	       \
				     __FUNCTION__, __FILE__, __LINE__,	\
				     _message_); fflush(stderr);}while(0);
#endif

#define SET_CMD         0x0001
#define ADD_CMD         0x0002
#define GET_CMD         0x0004
#define QUIT_CMD        0x0008

#define TCP             0x0001
#define UDP             0x0002
#define UNIX_SOCKET     0x0004

#define DEFAULT_PORT     11211
#define DEFAULT_THREADS      1
#define DEFAULT_COMMANDS     1
#define DEFAULT_MAX_KEY   1000
#define DEFAULT_DATA_LEN  1024

#define MAX_LINE         82000
#define MAX_ADDR_LEN        64
#define MAX_PORT_NO      65535
#define MAX_THREADS       1024
#define MAX_COMMANDS     65535
#define MAX_KEY          65535
#define MAX_DATA_LEN     40960


/*
 * type definition
 */
typedef struct {
    char addr[MAX_ADDR_LEN];
    int port;
    int thread_num;
    int command_num;
    int max_key;
    int command;
    int data_len;
    int verbose;
    int type;
#ifdef _DEBUG_
    int debug;
#endif
    bool single_command;
} sysval_t;


struct stat_time {
    struct timeval begin;
    struct timeval end;
};
typedef struct stat_time stat_data_t;

/*  command format */
const static char set_cmd_fmt[] = "set %d %u %s %u\r\n%s\r\n";
const static char add_cmd_fmt[] = "add %d %u %s %u\r\n%s\r\n";
const static char get_cmd_fmt[] = "get %d\r\n";
const static char quit_cmd_fmt[] = "quit\r\n";

/*
 * connect
 */
static void master_thread(void);
static double get_interval(struct timeval, struct timeval);
static int do_close(const int);
static int do_connect(const char *, const int);
static int connect_mc(void);
static int build_mc_cmd(char *, const int, const int, const int,
			const char *, const unsigned int, const unsigned long int);
static int do_cmd(const int, const char *, const int, const unsigned long int);
static void send_cmd(const int, const int, char *, char *);
static void send_quit_cmd(const int, const int, char *, const int);
static void connector_thread(void *);
static void usage(void);
static int str_cmp(const char *, const char *);
static void check_opt(int, char **);
static void init_sysval(void);

/*
 * global variables
 */
static sysval_t sysval;
static pthread_t *connector_tptr;
static pthread_t tid;
static stat_data_t *stat_data;
static pthread_mutex_t begin_mtx;
static pthread_cond_t begin_cond;
static unsigned int begin_thread_num;
static pthread_mutex_t end_mtx;
static pthread_cond_t end_cond;
static unsigned int end_thread_num;

static struct timeval stat_data_begin;
static struct timeval stat_data_end;

static int buff_size;
static int data_size;

#define DATA_SIZE  (sysval.data_len * 2 + 1)
#define BUFF_SIZE  (sysval.data_len * 2 + 100)

/*
 * master
 */
static void master_thread(void)
{
    int i;
    double tmp_itvl;
    double min_itvl = 0x7fffffff;
    double ave_itvl = 0.0;
    double max_itvl = 0.0;
    long double itvl = 0.0;
#ifndef __CBMC__
    assert(0 < sysval.thread_num && sysval.thread_num <= MAX_THREADS);
    assert(0 < sysval.command_num && sysval.command_num <= MAX_COMMANDS);
    assert(sysval.command == SET_CMD || sysval.command == ADD_CMD || sysval.command == GET_CMD);
    assert(sysval.type == TCP || sysval.type == UDP || sysval.type == UNIX_SOCKET);
#endif

    /*
     * wait for all threads end 
     */
    pthread_mutex_lock(&end_mtx);
    while (sysval.thread_num != end_thread_num)
	pthread_cond_wait(&end_cond, &end_mtx);
    pthread_mutex_unlock(&end_mtx);

    /*
     * display result 
     */
    gettimeofday(&stat_data_end, NULL);

    for (i = 0; i < sysval.thread_num; i++) {
	tmp_itvl = get_interval(stat_data[i].begin, stat_data[i].end);
#ifdef __CBMC__
	__CPROVER_assume(0.0 <= tmp_itvl);
#else
	assert(0.0 <= tmp_itvl);
#endif
	itvl += tmp_itvl;
	if (max_itvl < tmp_itvl)
	    max_itvl = tmp_itvl;
	if (tmp_itvl < min_itvl)
	    min_itvl = tmp_itvl;
	if (1 <= sysval.verbose)
	    fprintf(stdout, "thread(%d) end %f[sec]\n", i, tmp_itvl);
    }

    ave_itvl = (double) (itvl / sysval.thread_num);
    tmp_itvl = get_interval(stat_data_begin, stat_data_end);

#ifdef __CBMC__
    __CPROVER_assume(min_itvl <= max_itvl);
    __CPROVER_assume(min_itvl <= ave_itvl && ave_itvl <= max_itvl);
#endif
    assert(min_itvl <= max_itvl);
    assert(min_itvl <= ave_itvl && ave_itvl <= max_itvl);
    assert(0.0 <= tmp_itvl);

    fprintf(stdout, "condition =>\n");
    if (sysval.type == UNIX_SOCKET)
	fprintf(stdout, "\tconnect to localhost:(%s)\n", sysval.addr);
    else
	fprintf(stdout, "\tconnect to %s %s port %d\n", sysval.addr,
		(sysval.type == TCP ? "TCP" : "UDP"), sysval.port);
    if (sysval.command == SET_CMD)
	fprintf(stdout, "\tcommand = set\n");
    else if (sysval.command == ADD_CMD)
	fprintf(stdout, "\tcommand = add\n");
    else if (sysval.command == GET_CMD)
	fprintf(stdout, "\tcommand = get\n");
    if (sysval.thread_num > 1)
      fprintf(stdout, "\t%d threads run\n", sysval.thread_num);
    else
      fprintf(stdout, "\t%d thread run\n", sysval.thread_num);

    if (sysval.command_num > 1)
      fprintf(stdout, "\tsend %d commands a thread, ", sysval.command_num);
    else
      fprintf(stdout, "\tsend %d command a thread, ", sysval.command_num);
    if (sysval.command_num * sysval.thread_num > 1)
      fprintf(stdout, "total %d commands\n", sysval.command_num * sysval.thread_num);
    else
      fprintf(stdout, "total %d command\n", sysval.command_num * sysval.thread_num);
    fprintf(stdout, "\taverage data length = %d\n", sysval.data_len);
    fprintf(stdout, "result =>\n\tinterval =  %f [sec]\n", tmp_itvl);
    if (tmp_itvl != 0.0)
	fprintf(stdout, "\tperformance =  %f [commands/sec]\n",
		(sysval.command_num * sysval.thread_num) / tmp_itvl);
    fprintf(stdout,
	    "\tthread info:\n\t  ave. = %f[sec], min = %f[sec], max = %f[sec]\n",
	    ave_itvl, min_itvl, max_itvl);

    free(stat_data);
}


static double get_interval(struct timeval bt, struct timeval et)
{
    double b, e;

    b = bt.tv_sec + (double) bt.tv_usec * 1e-6;
    e = et.tv_sec + (double) et.tv_usec * 1e-6;
#ifndef __CBMC__
    assert(b <= e);
#endif
    return e - b;
}


/*
 * connector
 */
static int do_close(const int fd)
{
    return close(fd);
}

static int do_connect(const char *addr, const int port)
{
    int fd, sockopt = 1;
    struct sockaddr_in serv_addr_in;
    struct sockaddr_un serv_addr_un;

#ifndef __CBMC__
    assert(addr[0] != '\0');
#else
    __CPROVER_assume(sysval.type == TCP || sysval.type == UDP || sysval.type == UNIX_SOCKET);
#endif
    if (sysval.type == UNIX_SOCKET) {
	/* UNIX STREAM SOCKET */
	bzero((char *) &serv_addr_un, sizeof(serv_addr_un));
	serv_addr_un.sun_family = AF_LOCAL;
	strncpy(serv_addr_un.sun_path, addr, sizeof(serv_addr_un.sun_path) - 1);
	if ((fd = socket(AF_LOCAL, SOCK_STREAM, 0)) < 0) {
	    elog("can't open unix stream socket");
	    exit(-1);
	}
	if (connect(fd, (struct sockaddr *) &serv_addr_un, sizeof(serv_addr_un)) < 0) {
	    do_close(fd);
	    fd = -1;
	}
    } else {
	/* TCP or UDP */
	assert(sysval.type == TCP || sysval.type == UDP);
	bzero((char *) &serv_addr_in, sizeof(serv_addr_in));
	serv_addr_in.sin_family = AF_INET;
	serv_addr_in.sin_addr.s_addr = inet_addr(addr);
	serv_addr_in.sin_port = htons(port);

	if (sysval.type == TCP) {
	    if ((fd = socket(AF_INET, SOCK_STREAM, 0)) < 0) {
		elog("can't open stream socket");
		exit(-1);
	    }
	} else if (sysval.type == UDP) {
	    if ((fd = socket(AF_INET, SOCK_DGRAM, 0)) < 0) {
		elog("can't open datagram socket");
		exit(-1);
	    }
	} else {
	    assert(0);		// never claim
	}

	setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &sockopt, sizeof(sockopt));
	if (connect(fd, (struct sockaddr *) &serv_addr_in, sizeof(serv_addr_in)) < 0) {
	    do_close(fd);
	    fd = -1;
	}
    }
    return fd;
}

static int connect_mc()
{
    int fd = -1;
    if ((fd = do_connect(sysval.addr, sysval.port)) == -1) {
	fprintf(stderr, "Error: can not connect to memcached\n");
	if (sysval.type == UNIX_SOCKET)
	    fprintf(stderr, "\tHint => Check permission of unix socket path(%s).\n", sysval.addr);
	exit(-1);
    }
    assert(fd != -1);
    return fd;
}

static int
build_mc_cmd(char *buff, const int buff_size, const int cmd_type,
	     const int key, const char *val, const unsigned int val_len, const unsigned long int id)
{
    int len = -1;
    int s;
#ifdef __CBMC__
    buff = (char *) malloc(buff_size);
    __CPROVER_assume(sysval.type == TCP || sysval.type == UDP || sysval.type == UNIX_SOCKET);
    __CPROVER_assume(buff_size == (BUFF_SIZE));
#else
    assert(sysval.type == TCP || sysval.type == UDP || sysval.type == UNIX_SOCKET);
#endif

    memset(buff, 0, buff_size);
    s = (sysval.type == UDP) ? 8 : 0;

    switch (cmd_type) {
    case SET_CMD:
	sprintf(&buff[s], set_cmd_fmt, key, (unsigned int) 0, "0", val_len, val);
	len = strlen(&buff[s]);
	break;
    case ADD_CMD:
	sprintf(&buff[s], add_cmd_fmt, key, (unsigned int) 0, "0", val_len, val);
	len = strlen(&buff[s]);
	break;
    case GET_CMD:
	sprintf(&buff[s], get_cmd_fmt, key);
	len = strlen(&buff[s]);
	break;
    case QUIT_CMD:
	sprintf(&buff[s], quit_cmd_fmt);
	len = strlen(&buff[s]);
	break;
    default:
	assert(0);
	fprintf(stderr, "%s():%s:%u: %d command not supported\n",
		__FUNCTION__, __FILE__, __LINE__, cmd_type);
	abort();
    }

    if (sysval.type == UDP) {
	buff[0] = (char) ((id & 0x0000ff00) >> 8);
	buff[1] = (char) id & 0x000000ff;	/* Request ID */
	buff[2] = (char) 0;
	buff[3] = (char) 0;	/* Sequence number */
	buff[4] = (char) 0;
	buff[5] = (char) 1;	/* Total number of datagrams: must be "01" */
	buff[6] = (char) 0;
	buff[7] = (char) 0;	/* Reserve must be 0 */
	len += s;
    }

    return len;
}

static int do_cmd(const int fd, const char *cmd, const int cmd_len, const unsigned long int id)
{
    int ret, len;
    struct timeval tv;
    fd_set fds;
    char result[MAX_LINE];

#ifdef _DEBUG_
    if (2 <= sysval.debug) {
	if (sysval.type == UDP)
	    fprintf(stdout, "CMD: %s\n", &cmd[8]);
	else
	    fprintf(stdout, "CMD: %s\n", cmd);
    }
#endif

    FD_ZERO(&fds);
    FD_SET(fd, &fds);
    tv.tv_sec = 0;
    tv.tv_usec = 0;

    /* send command to memcached  */
    if (send(fd, cmd, cmd_len, 0) != cmd_len) {
	elog("send error");
	return -1;
    }

    /* recieve result */
    len = -1;
    ret = select(fd + 1, &fds, NULL, NULL, NULL);
    if (ret == 0) {		/* timeout */
	elog("select timeout");
	return 0;
    }
    if (FD_ISSET(fd, &fds)) {
	/* DO NOTHING  */
	if ((len = recv(fd, result, sizeof(result), 0)) < 0) {
	    elog("read error");
	    return -1;
	}
    }

    if (sysval.type == UDP) {
	if ((result[0] & 0x000000ff) != ((id & 0x0000ff00) >> 8)
	    || (result[1] & 0x000000ff) != (id & 0x00000ff))
	    fprintf(stderr, "Error: UDP RequestID error\n");
    }
#ifdef _DEBUG_
    if (2 <= sysval.debug) {
	if (sysval.type == UDP)
	    fprintf(stdout, "RESULT: %s\n", &result[8]);
	else
	    fprintf(stdout, "RESULT: %s\n", result);
    }
#endif
    return len;
}

static void send_cmd(const int fd, const int id, char *data, char *buff)
{
    int key, msg_len, str_len;
    int _rand = rand();
    double r;

#ifndef __CBMC__
    assert(fd != -1);
    assert(0 <= _rand && _rand <= RAND_MAX);
    assert(0 < sysval.data_len && sysval.data_len <= MAX_DATA_LEN);
    assert(0 < sysval.max_key && sysval.max_key <= MAX_KEY);
    assert(data_size == (DATA_SIZE));
    assert(buff_size == (BUFF_SIZE));
#endif

    /* check: r     */
#ifdef __CBMC__
    __CPROVER_assume(0 <= _rand && _rand <= RAND_MAX);
#endif
    r = (double) (_rand / (RAND_MAX + 1.0));
    assert(0.0 <= r && r < 1.0);

    /* check: key     */
#ifdef __CBMC__
#undef MAX_KEY
#define MAX_KEY 100
    sysval.max_key = 10; // dummy
    __CPROVER_assume(0 < sysval.max_key && sysval.max_key <= MAX_KEY);
#endif
    key = 1 + (int) ((double) (sysval.max_key * r));
    assert(0 < key && key <= sysval.max_key);

    /* check: str_len     */
#ifdef __CBMC__
    sysval.data_len = 10; // dummy
    __CPROVER_assume(0 < sysval.data_len && sysval.data_len <= MAX_DATA_LEN);
    data_size = DATA_SIZE;
#endif
    str_len = 1 + (int) ((double) ((sysval.data_len * 2) * r));
    assert(0 < str_len && str_len < data_size);

    /* check: data     */
#ifdef __CBMC__
    char *data = (char *) malloc(data_size);
#endif
    data[str_len] = '\0';

    msg_len = build_mc_cmd(buff, buff_size, sysval.command, key, data,
			   /*strlen(data) = */ str_len, id);
    assert(msg_len <= buff_size);
    /* marking */
    data[str_len] = 'X';

    do_cmd(fd, buff, msg_len, id);
}

static void send_quit_cmd(const int fd, const int id, char *buff, const int buff_size)
{
    int len;

    len = build_mc_cmd(buff, buff_size, QUIT_CMD, 0, NULL, 0, id);
    do_cmd(fd, buff, len, id);
    do_close(fd);
}

static void connector_thread(void *arg)
{
    const intptr_t no = (intptr_t) arg;
    int fd;
    int i;
    unsigned long int id;
    char *buff, *data;

#ifndef __CBMC__
    assert(0 < sysval.data_len && sysval.data_len <= MAX_DATA_LEN);
    assert(data_size == (DATA_SIZE));
    assert(buff_size == (BUFF_SIZE));
    assert(sysval.thread_num <= MAX_THREADS);
    assert(0 < sysval.command_num && sysval.command_num <= MAX_COMMANDS);
    assert(sysval.type == TCP || sysval.type == UDP || sysval.type == UNIX_SOCKET);
    assert(0 <= no && no < sysval.thread_num);
#endif

    if ((buff = (char *) malloc(buff_size)) == NULL) {
	elog("malloc error");
	exit(-1);
    }
    if ((data = (char *) malloc(data_size)) == NULL) {
	elog("malloc error");
	exit(-1);
    }
#ifdef __CBMC__
    __CPROVER_assume(data_size == (DATA_SIZE));
#endif
    memset(data, 79, (size_t) data_size);	/* char'79' = 'O' */
    data[data_size - 1] = '\0';

    /*
     * increment begin_thread_num, 
     * and wait for broadcast signal from last created thread
     */
    if (sysval.thread_num != 1) {
	pthread_mutex_lock(&begin_mtx);
	begin_thread_num++;
	if (begin_thread_num == sysval.thread_num)
	    pthread_cond_broadcast(&begin_cond);
	else {
	    while (begin_thread_num < sysval.thread_num)
		pthread_cond_wait(&begin_cond, &begin_mtx);
	}
	pthread_mutex_unlock(&begin_mtx);

	assert(begin_thread_num == sysval.thread_num);
    }

    gettimeofday(&stat_data[no].begin, NULL);

    /*  prepare a random seed */
    srand((unsigned int) (stat_data[no].begin.tv_sec % RAND_MAX));

    /* */
    if (sysval.single_command == false || sysval.type == UDP)
	fd = connect_mc();

    /*
     * main loop 
     */
    id = sysval.command_num * (no + 1);
    for (i = 0; i < sysval.command_num; i++) {
	id++;
	if (sysval.single_command == true && sysval.type != UDP)
	    fd = connect_mc();

	/* send command */
	send_cmd(fd, id, data, buff);

	if (sysval.single_command == true && sysval.type != UDP)
	    send_quit_cmd(fd, id, buff, buff_size);	/*  send quit command */

    }				// for

    if (sysval.single_command == false && sysval.type != UDP)
	send_quit_cmd(fd, id, buff, buff_size);	/*  send quit command */

    /*
     * send signal 
     */
    gettimeofday(&stat_data[no].end, NULL);
    pthread_mutex_lock(&end_mtx);
    end_thread_num++;
    pthread_cond_signal(&end_cond);
    pthread_mutex_unlock(&end_mtx);

    free(buff);
    free(data);
}


static void usage(void)
{
    fprintf(stderr, "mcb -- simple memcached benchmark\n");
    fprintf(stderr, "usage: mcb -c {set|add|get} [OPTIONS]\n");
    fprintf(stderr, "\t-c {set|add|get}\t command type\n");
    fprintf(stderr, "\t-a <address>\t\t memcached address[127.0.0.1]\n");
    fprintf(stderr, "\t-p <num>\t\t memcached port[%d]\n", DEFAULT_PORT);
    fprintf(stderr, "\t-T {TCP|UDP|UNIX_SOCKET} connection type[TCP]\n");
    fprintf(stderr, "\t-f <filepath>\t\t unix socket path\n");
    fprintf(stderr, "\t-t <1-%d>\t\t number of threads to run[%d]\n", MAX_THREADS, DEFAULT_THREADS);
    fprintf(stderr, "\t-n <1-%d>\t\t number of commands to send[%d]\n", MAX_COMMANDS, DEFAULT_COMMANDS);
    fprintf(stderr, "\t-m <1-%d>\t\t max key[%d]\n", MAX_KEY, DEFAULT_MAX_KEY);
    fprintf(stderr, "\t-l <1-%d>\t\t average data length[%d]\n", MAX_DATA_LEN, DEFAULT_DATA_LEN);
    fprintf(stderr, "\t-v\t\t\t verbose\n");
    fprintf(stderr, "\t-s\t\t\t connect to memcached for each command\n");
    fprintf(stderr, "\t-h\t\t\t help\n");
#ifdef _DEBUG_
    fprintf(stderr, "\t-d <0-2>\t\t debug level\n");
#endif
}


static void init_sysval(void)
{
    sysval.addr[0] = '\0';
    sysval.port = DEFAULT_PORT;
    sysval.thread_num = DEFAULT_THREADS;
    sysval.command_num = DEFAULT_COMMANDS;
    sysval.max_key = DEFAULT_MAX_KEY;
    sysval.data_len = DEFAULT_DATA_LEN;
    sysval.command = -1;
    sysval.verbose = 0;
    sysval.type = TCP;
#ifdef _DEBUG_
    sysval.debug = 0;
#endif
    sysval.single_command = false;
}

static int str_cmp(const char *s1, const char *s2)
{
    int i = 0;
    while (toupper((unsigned char) s1[i]) == toupper((unsigned char) s2[i])) {
	if (s1[i] == '\0')
	    return 0;
	i++;
    }
    return toupper((unsigned char) s1[i]) - toupper((unsigned char) s2[i]);
}


static void check_opt(int argc, char **argv)
{
    char c;
    int max_key;

#ifdef _DEBUG_
    while ((c = getopt(argc, argv, "a:p:t:n:m:c:l:vVhsd:T:f:")) != -1) {
#else
    while ((c = getopt(argc, argv, "a:p:t:n:m:c:l:vVhsT:f:")) != -1) {
#endif
	switch (c) {
	case 'a':		/* server address */
	case 'f':		/* unix socket path */

	    if (MAX_ADDR_LEN <= strlen(optarg)) {
		fprintf(stderr, "Error: address is too long. (max %d byte)\n", MAX_ADDR_LEN);
		exit(-1);
	    }
	    strcpy(sysval.addr, optarg);
	    break;
	case 'p':		/* server port */
	    sysval.port = strtol(optarg, NULL, 10);
	    if (sysval.port <= 0 || MAX_PORT_NO < sysval.port) {
		fprintf(stderr, "Error: port number %d is not valid\n", sysval.port);
		exit(-1);
	    }
	    break;
	case 't':		/* number of thread */
	    sysval.thread_num = strtol(optarg, NULL, 10);
	    if (MAX_THREADS < sysval.thread_num) {
		fprintf(stderr,
			"Error: thread number %d is not valid. max %d\n",
			sysval.thread_num, MAX_THREADS);
		exit(-1);
	    }
	    if (sysval.thread_num <= 0) {
		fprintf(stderr, "Error: thread number %d is not valid\n", sysval.thread_num);
		exit(-1);
	    }
	    break;
	case 'n':		/* number of command */
	    sysval.command_num = strtol(optarg, NULL, 10);
	    if (sysval.command_num <= 0 || MAX_COMMANDS < sysval.command_num) {
		fprintf(stderr,
			"Error: command number %d is not valid. max %d commands\n",
			sysval.command_num, MAX_COMMANDS);
		exit(-1);
	    }
	    break;
	case 'm':		/* max key value */
	    max_key = strtol(optarg, NULL, 10);
	    if (max_key <= 0 || MAX_KEY < max_key) {
		fprintf(stderr,
			"WARNING: max key %d is not valid. Set default(%d).\n",
			max_key, DEFAULT_MAX_KEY);
		max_key = DEFAULT_MAX_KEY;
	    }
	    sysval.max_key = max_key;
	    break;
	case 'c':		/* command type */
	    if (str_cmp(optarg, "set") == 0)
		sysval.command = SET_CMD;
	    else if (str_cmp(optarg, "add") == 0)
		sysval.command = ADD_CMD;
	    else if (str_cmp(optarg, "get") == 0)
		sysval.command = GET_CMD;
	    else {
		usage();
		exit(-1);
	    }
	    break;
	case 'l':		/* data length */
	    sysval.data_len = strtol(optarg, NULL, 10);
	    if (sysval.data_len <= 0 || MAX_DATA_LEN < sysval.data_len) {
		fprintf(stderr,
			"Error: data_length %d is not valid (1-%d)\n",
			sysval.data_len, MAX_DATA_LEN);
		exit(-1);
	    }
	    break;
	case 'v':
	    sysval.verbose = 1;
	    break;
	case 'V':
	    sysval.verbose = 2;
	    break;
#ifdef _DEBUG_
	case 'd':
	    sysval.debug = strtol(optarg, NULL, 10);
	    break;
#endif
	case 's':
	    sysval.single_command = true;
	    break;
	case 'T':		/* connection type */
	    if (str_cmp(optarg, "TCP") == 0) {
		sysval.type = TCP;
	    } else if (str_cmp(optarg, "UDP") == 0) {
		sysval.type = UDP;
	    } else if (str_cmp(optarg, "SOCKET") == 0 || str_cmp(optarg, "UNIX_SOCKET") == 0) {
		sysval.type = UNIX_SOCKET;
	    } else {
		fprintf(stderr, "Error:  %s is not valid. \n", optarg);
		exit(-1);
	    }
	    break;
	case 'h':		/* help */
	    usage();
	    exit(0);
	default:
	    fprintf(stderr, "ERROR: option error: -%c is not valid\n", optopt);
	    exit(-1);
	}
    }
}


int main(int argc, char **argv)
{
    int i;
    void *ret = NULL;

    /*
     * init 
     */
    begin_mtx = (pthread_mutex_t) PTHREAD_MUTEX_INITIALIZER;
    begin_cond = (pthread_cond_t) PTHREAD_COND_INITIALIZER;
    end_mtx = (pthread_mutex_t) PTHREAD_MUTEX_INITIALIZER;
    end_cond = (pthread_cond_t) PTHREAD_COND_INITIALIZER;
    begin_thread_num = 0;
    end_thread_num = 0;
    init_sysval();

    /*
     * option check
     */
    check_opt(argc, argv);

    if (sysval.command == -1) {
	fprintf(stderr, "error: option -c not set\n");
	usage();
	exit(-1);
    }
    if (sysval.type == UNIX_SOCKET && sysval.addr[0] == '\0') {
	fprintf(stderr, "error: option -f not set\n");
	usage();
	exit(-1);
    }
    if (sysval.addr[0] == '\0')
	strcpy(sysval.addr, "127.0.0.1");

    assert(0 < strlen(sysval.addr) && strlen(sysval.addr) < MAX_ADDR_LEN);
    assert(0 < sysval.port && sysval.port <= MAX_PORT_NO);
    assert(0 < sysval.thread_num && sysval.thread_num <= MAX_THREADS);
    assert(0 < sysval.command_num && sysval.command_num <= MAX_COMMANDS);
    assert(0 < sysval.max_key && sysval.max_key <= MAX_KEY);
    assert(0 < sysval.data_len && sysval.data_len <= MAX_DATA_LEN);
    assert(sysval.command == SET_CMD || sysval.command == ADD_CMD || sysval.command == GET_CMD);
    assert(sysval.type == TCP || sysval.type == UDP || sysval.type == UNIX_SOCKET);
    assert(sysval.single_command == true || sysval.single_command == false);

    /*
     * set array size: data, buff
     */
    data_size = DATA_SIZE;
    buff_size = BUFF_SIZE;

    /*
     * 
     */
    if ((stat_data = calloc(sysval.thread_num, sizeof(stat_data_t))) == NULL) {
	elog("calloc error");
	exit(-1);
    }
    if ((connector_tptr = calloc(sysval.thread_num, sizeof(pthread_t))) == NULL) {
	elog("calloc error");
	exit(-1);
    }

    gettimeofday(&stat_data_begin, NULL);
    if (pthread_create(&tid, (void *) NULL, (void *) master_thread, (void *) NULL) != 0) {
	elog("pthread_create() error");
	exit(-1);
    }

    for (i = 0; i < sysval.thread_num; i++)
      if (pthread_create(&connector_tptr[i], NULL, (void *) connector_thread, (void *)(intptr_t) i) != 0) {
	    elog("pthread_create() error");
	    exit(-1);
	}

    if (pthread_join(tid, &ret)) {
	elog("pthread_join() error");
	exit(-1);
    }

    for (i = 0; i < sysval.thread_num; i++)
	if (pthread_join(connector_tptr[i], &ret)) {
	    elog("pthread_join() error");
	    exit(-1);
	}

    pthread_cond_destroy(&begin_cond);
    pthread_cond_destroy(&end_cond);
    free(connector_tptr);

    return 0;
}

// EOF
