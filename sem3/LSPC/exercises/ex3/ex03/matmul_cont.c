#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>

#include <mpi.h>

#include <unistd.h>

#define DIM_LEN (1024*2)

void init_mat(char *mat);
void cal_prod(char *mat_1,
			  char *mat_2,
			  unsigned long long **prod);
unsigned long long get_time();
void print_mat_llu(unsigned long long *mat);
void print_mat_char(char *mat);

void distribute_matrix_rows(char *mat);
void distribute_matrix_cols(char *mat);
void gather_product(unsigned long long **prod);

int row_div;
int col_div;

int my_rank;
int comm_size;

int main(int argc, char* argv[])
{
	char *mat_1;
	char *mat_2;
	unsigned long long **prod;

	my_rank;
	comm_size;

	MPI_Init(&argc, &argv);

	MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);
	MPI_Comm_size(MPI_COMM_WORLD, &comm_size);

	unsigned long long start_time = get_time();
	if(my_rank == 0)
	{
		printf("Starting app at time: %llu\n", start_time);
	}
	
	row_div = 1;
	col_div = 1;

	if(my_rank != 0)
	{
		col_div = (int)floor(sqrt((double)comm_size));
		while(comm_size % col_div != 0)
		{
			col_div--;
		}
		if(col_div == 0)
		{
			fprintf(stderr, "Error: col_div is zero!!\n");
		}
		row_div = comm_size / col_div;
	}

	mat_1 = malloc(sizeof(char) * DIM_LEN * DIM_LEN / row_div);
	mat_2 = malloc(sizeof(char) * DIM_LEN * DIM_LEN / col_div);
	prod = malloc(sizeof(unsigned long long *) * DIM_LEN / row_div);

	int i;
	for(i = 0; i < DIM_LEN / row_div; i++)
	{
		prod[i] = malloc(sizeof(unsigned long long) * DIM_LEN / col_div);
	}
	

	unsigned long long atime = get_time();
	if(my_rank == 0)
	{
		printf("Time spent in allocation: %llu\n", atime - start_time);
	}

	if(my_rank == 0)
	{
		init_mat(mat_1);
		init_mat(mat_2);
	}

	if(my_rank == 0)
	{
		col_div = (int)floor(sqrt((double)comm_size));
		while(comm_size % col_div != 0)
		{
			col_div--;
		}
		if(col_div == 0)
		{
			fprintf(stderr, "Error: col_div is zero!!\n");
		}
		row_div = comm_size / col_div;
	}
	unsigned long long itime = get_time();
	if(my_rank == 0)
	{
		fprintf(stderr, "Time spent in initialization: %llu\n", itime - atime);
	}

	distribute_matrix_rows(mat_1);
	distribute_matrix_cols(mat_2);

	unsigned long long dtime = get_time();
	if(my_rank == 0)
	{
		fprintf(stderr, "Time spent in distributing matrices: %llu\n", dtime - itime);
	}
	cal_prod(mat_1, mat_2, prod);
	unsigned long long ptime = get_time();

	if(my_rank == 0)
	{
		fprintf(stderr, "Time spent in multiplication: %llu\n", ptime - dtime);
	}

	gather_product(prod);
	unsigned long long gtime = get_time();
	if(my_rank == 0)
	{
		printf("Time spent in gathering: %llu\n", gtime - ptime);
		printf("Total time spent in application: %llu\n", gtime - start_time);
	}

	MPI_Finalize();
	return 0;
}

void distribute_matrix_rows(char *lmat)
{
	int i, j;
	int row_group_size = DIM_LEN / row_div;
	MPI_Status stat;
	int displacement[comm_size];
	int scount[comm_size];

	for(i = 0; i < comm_size; i++)
	{
		displacement[i] = floor(i / col_div) * row_group_size;
		scount[i] = row_group_size;
	}
	MPI_Scatterv(lmat, scount, displacement, MPI_CHAR, lmat, row_group_size, MPI_CHAR, 0, MPI_COMM_WORLD);
}

void distribute_matrix_cols(char *mat)
{
	int i, j;
	int cols_group_size = DIM_LEN / col_div;
	MPI_Status stat;
	int displacement[comm_size];
	int scount[comm_size];

	for(i = 0; i < comm_size; i++)
	{
		displacement[i] = floor(i / row_div) * cols_group_size;
		scount[i] = cols_group_size;
	}
	MPI_Scatterv(mat, scount, displacement, MPI_CHAR, mat, cols_group_size, MPI_CHAR, 0, MPI_COMM_WORLD);
}

void gather_product(unsigned long long **prod)
{
	int i, j;
	int cols_group_size = DIM_LEN / col_div;
	int rows_group_size = DIM_LEN / row_div;
	MPI_Status stat;

	if(my_rank == 0)
	{
		for(i = 1; i < comm_size; i++)
		{
			int col_disp = (i % col_div);
			int row_disp = floor(i / col_div);
			for(j = 0; j < rows_group_size; j++)
			{
				MPI_Recv(&prod[row_disp * rows_group_size + j][col_disp * cols_group_size], cols_group_size, MPI_UNSIGNED_LONG_LONG, i, 0, MPI_COMM_WORLD, &stat);
			}
		}
	}
	else
	{
		for(j = 0; j < rows_group_size; j++)
		{
			MPI_Ssend(prod[j], cols_group_size, MPI_UNSIGNED_LONG_LONG, 0, 0, MPI_COMM_WORLD);
		}
	}
}

void init_mat(char *mat)
{
	int i, j;
	for(i = 0; i < DIM_LEN; i++)
	{
		for(j = 0; j < DIM_LEN; j++)
		{
			mat[i * DIM_LEN + j] = (random() % 9) + 1;
		}
	}
}
void cal_prod(char *mat_1,
			  char *mat_2,
			  unsigned long long **prod)
{
	int i, j, k;
	for(i = 0; i < DIM_LEN / row_div; i++)
	{
		for(j = 0; j < DIM_LEN / col_div; j++)
		{
			prod[i][j] = 0;
			for(k = 0; k < DIM_LEN; k++)
			{
				prod[i][j] += (mat_1[i * DIM_LEN + k] * mat_2[j * DIM_LEN + k]);
			}
		}
	}
}

unsigned long long get_time()
{
	struct timespec ctime; 
	clock_gettime(CLOCK_REALTIME, &ctime);
	unsigned long long time = ctime.tv_sec * 1e9 + ctime.tv_nsec;
	return time;
}

void print_mat_llu(unsigned long long *mat)
{
	int i, j;
	for(i = 0; i < DIM_LEN; i++)
	{
		for(j = 0; j < DIM_LEN; j++)
		{
			printf("%llu ", mat[i * DIM_LEN + j]);
		}
		printf("\n");
	}
}

void print_mat_char(char *mat)
{
	int i, j;
	for(i = 0; i < DIM_LEN; i++)
	{
		for(j = 0; j < DIM_LEN; j++)
		{
			printf("%c ", mat[i * DIM_LEN + j]);
		}
		printf("\n");
	}
}

