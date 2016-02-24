

CC=mpicc
CFLAGS=-g -O0
LDFLAGS=-lrt -g 

all: matmul_seq matmul_mpi matmul_trans matmul_cont

matmul_cont: matmul_cont.o
	$(CC) $(LDFLAGS) $< -o $@

matmul_trans: matmul_trans.o
	$(CC) $(LDFLAGS) $< -o $@

matmul_mpi: matmul_mpi.o
	$(CC) $(LDFLAGS) $< -o $@

matmul_seq: matmul_seq.o
	$(CC) $(LDFLAGS) $< -o $@

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm *.o matmul_seq matmul_mpi matmul_trans matmul_cont
