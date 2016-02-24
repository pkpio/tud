#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

#include <mpi.h>

#define DIM_LEN (16)

void init_mat(int* mat);
void init_mat_zero(int* mat);
void print_mat_rows(int* mat, int count, int start_point);
void print_mat_cols(int* mat, int count, int start_point);
void mat_mul(int* mat_1, int* mat_2, int* mat_r, int rcnt, int ccnt);
void print_mat(int* mat, int rows, int cols);

unsigned long long get_time();

int comm_rank;
int comm_size;

int *mat_1, *mat_2, *mat_r;

int main(int argc, char* argv[])
{
	MPI_Init(&argc, &argv);

	MPI_Comm_rank(MPI_COMM_WORLD, &comm_rank);
	MPI_Comm_size(MPI_COMM_WORLD, &comm_size);

	int sqcs = sqrt(comm_size);
	if(comm_size != sqcs * sqcs)
	{
		MPI_Finalize();
		return -1;
	}

	int proc_cnt = sqrt(comm_size);

	int dim_cnt = DIM_LEN / proc_cnt;

	mat_1 = malloc(sizeof(int) * DIM_LEN * DIM_LEN);
	mat_2 = malloc(sizeof(int) * DIM_LEN * DIM_LEN);
	mat_r = malloc(sizeof(int) * DIM_LEN * DIM_LEN);

	if(comm_rank == 0)
	{
		init_mat(mat_1);
		init_mat(mat_2);
		init_mat_zero(mat_r);
	}
	else
	{
		init_mat_zero(mat_1);
		init_mat_zero(mat_2);
		init_mat_zero(mat_r);
	}

	unsigned long long start_time = get_time();

	/* Step 1: */
	/* Create datatypes for rows, columns and tiles */
	/* Define the extent large enough to send a process's share in one transfer */
	MPI_Datatype row_type;
	MPI_Datatype col_type;

	// Row definition
	MPI_Type_vector(DIM_LEN, DIM_LEN, 0, MPI_INT, &row_type);
	MPI_Type_commit(&row_type);

	// Column definition
	MPI_Type_vector(DIM_LEN, 1, DIM_LEN, MPI_INT, &col_type);
	MPI_Type_commit(&col_type);
	
	/* Step 2: */
	/* Scatter rows among processes */
	/* The choice is either to use MPI_Scatterv or MPI_Send/MPI_Recv */
	/* Why can't the simple MPI_Scatter be used? */
	MPI_Status status;
	int *sendcnts;
	int *disps;
	sendcnts = malloc(sizeof(int) * comm_size);
	disps = malloc(sizeof(int) * comm_size);
	int i;
	for(i=0; i<comm_size; i++){
		sendcnts[i] = DIM_LEN / comm_size;
		disps[i] = i * (DIM_LEN / comm_size);
	}
	MPI_Scatterv(mat_1, sendcnts, disps, row_type, mat_1, DIM_LEN, row_type, 0, MPI_COMM_WORLD);

	//printf("\nRank : %d\n", comm_rank);
	//print_mat(mat_1, DIM_LEN, DIM_LEN);
	//printf("\n\n\n");


	/* Step 3: */
	/* Distribute the columns among processes */
	/* Is it possible to use MPI_Scatterv for columns? */
	/* What is the extent of the column data type? */
	MPI_Aint lb;
	MPI_Aint extent;
	MPI_Type_get_extent(col_type, &lb, &extent);
	//printf("LB : %d Extent : %d\n", lb, extent);
	
	// New col type after resizing
	MPI_Datatype ncol_type;
	MPI_Type_create_resized(col_type, 0, sizeof(int), &ncol_type);
        MPI_Type_get_extent(ncol_type, &lb, &extent);
        //printf("LB : %d Extent : %d\n", lb, extent);

	MPI_Scatterv(mat_2, sendcnts, disps, ncol_type, mat_2, DIM_LEN, ncol_type, 0, MPI_COMM_WORLD);

        //printf("\nRank : %d\n", comm_rank);
        //print_mat(mat_2, DIM_LEN, DIM_LEN);
        //printf("\n\n\n");

	unsigned long long dist_time = get_time();

	/* Step 4: */
	/* Each process calculates the product of its share */
	
	mat_mul(mat_1, mat_2, mat_r, dim_cnt, dim_cnt);

	unsigned long long mul_time = get_time();
	
	/* Step 5: */
	/* Gather all the product tiles at root (rank 0) */
	/* Can we use MPI_Gatherv for it? */
	/* What is the extent of the tile data type */
	printf("\nRank : %d\n", comm_rank);
        print_mat(mat_r, DIM_LEN, DIM_LEN);
        printf("\n\n\n");

	/* Step 6: */
	/* Free the created datatypes */

	/*
	unsigned long long end_time = get_time();
	unsigned long long dist_dur = dist_time - start_time;
	unsigned long long mul_dur = mul_time - dist_time;
	unsigned long long gather_dur = end_time - mul_time;
	unsigned long long total_dur = end_time - start_time;

	if(comm_rank == 0)
	{
		printf("** Total time taken: %llu\n", total_dur);
		printf("\tData distribution time: %llu\n", dist_dur);
		printf("\tMultiplication time: %llu\n", mul_dur);
		printf("\tGather time: %llu\n", gather_dur);
	}
	*/

	MPI_Finalize();
	return 0;
}

void mat_mul(int* mat_1, int* mat_2, int* mat_r, int rcnt, int ccnt)
{
	int i, j, k;
	for(i = 0; i < rcnt; i++)
	{
		for(j = 0; j < ccnt; j++)
		{
			mat_r[i * DIM_LEN + j] = 0;

			for(k = 0; k < DIM_LEN; k++)
			{
				mat_r[i * DIM_LEN + j] += mat_1[i * DIM_LEN + k] * mat_2[j + DIM_LEN * k];
			}
		}
	}
}

void print_mat(int* mat, int rows, int cols)
{
	int r, c;
	for(r = 0; r < rows; r++)
	{
		for(c = 0; c < cols; c++)
		{
			printf("%d ", mat[r * cols + c]);
		}
		printf("\n");
	}
}

void print_mat_cols(int* mat, int count, int start_point)
{
	int i, j;
	for(i = start_point; i < start_point + count; i++)
	{
		for(j = 0; j < DIM_LEN; j++)
		{
			printf("-%d", mat[i +  DIM_LEN * j]);
		}
		printf("\n");
	}
}

void print_mat_rows(int* mat, int count, int start_point)
{
	int i, j;
	for(i = start_point; i < start_point + count; i++)
	{
		for(j = 0; j < DIM_LEN; j++)
		{
			printf("%d ", mat[i * DIM_LEN + j]);
		}
		printf("\n");
	}
}

void init_mat(int* mat)
{
	int i, j, cnt = 0;
	for(i = 0; i < DIM_LEN; i++)
	{
		for(j = 0; j < DIM_LEN; j++)
		{
			mat[i * DIM_LEN + j] = cnt++;
		}
	}
}

void init_mat_zero(int* mat)
{
	int i, j, cnt = 0;
	for(i = 0; i < DIM_LEN; i++)
	{
		for(j = 0; j < DIM_LEN; j++)
		{
			mat[i * DIM_LEN + j] = cnt;
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

