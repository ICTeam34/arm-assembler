CC      = gcc
CFLAGS  = -Wall -g -D_POSIX_SOURCE -D_BSD_SOURCE -std=c99 -Werror -pedantic

.SUFFIXES: .c .o

.PHONY: all clean

all: assemble 

assemble: assemble.o

clean:
	rm -f $(wildcard *.o)
	rm -f assemble
