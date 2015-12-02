# mcb

mcb is a simple memcached benchmark. This has been tested by using CBMC(http://www.cprover.org/cbmc/), valgrind(http://valgrind.org/), and Intel Inspector XE.

## Compile

    $ cc -Wall -lpthread -o mcb mcb.c

## Usage

    usage: mcb -c {set|add|get} [OPTIONS]
    	   -c {set|add|get}         command type
    	   -a <address>             memcached address[127.0.0.1]
    	   -p <num>                 memcached port[11211]
    	   -T {TCP|UDP|UNIX_SOCKET} connection type[TCP]
    	   -f <file-path>           unix socket path
    	   -t <num>                 number of threads to run[1]
    	   -n <num>                 number of commands to send[1]
    	   -m <num>                 max key length[1000]
    	   -l <num>                 average data length[10]
    	   -v                       verbose
    	   -s                       connect to memcached for each command
    	   -h                       help

## Examples

Starting 10 threads, each thread sends one thousand "set" commands.

    $ mcb -c set -a 192.168.1.100 -p 11211 -t 10 -n 1000 -l 100
    condition =>
        connect to 192.168.1.100 TCP port 11211
            command = set
            10 threads run
            send 1000 commands a thread, total 10000 commands
            average data length = 100
    result =>
            interval =  0.419934 [sec]
            performance =  23813.263946 [commands/sec]
            thread info:
              ave. = 0.230296[sec], min = 0.047713[sec], max = 0.393719[sec]


Total execution time of all commands is 0.419934 seconds. Therefore, memcached can handle 23813.263946 commands per second.


If you want to use UDP, set '-T UDP' option.

    $ mcb -c set -a 192.168.1.100 -p 11211 -t 10 -n 1000 -l 100 -T UDP


If you want to use unix socket, set '-T UNIX_SOCKET' and '-f /domainsocket/dir/file' options.

    $ mcb -c set -t 10 -n 1000 -l 100 -T UNIX_SOCKET -f /tmp/memcached

## Author

Suzuki Hironobu: hironobu@interdb.jp
