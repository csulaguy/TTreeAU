CC = gcc
CFLAGS = -O2 -Wall
LIBS = -lncurses

tta: tta.c
	$(CC) $(CFLAGS) -o tta tta.c $(LIBS)

install: tta
	install -m 755 tta /usr/local/bin/tta

clean:
	rm -f tta
