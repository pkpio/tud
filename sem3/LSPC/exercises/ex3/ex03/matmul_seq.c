#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define DIM_LEN (1024*2)

void init_mat(char **mat);
void cal_prod(char **mat_1,
			  char **mat_2,
			  unsigned long long **prod);
unsigned long long get_time();
void print_mat_llu(unsigned long long **mat);
void print_mat_char(char **mat);

int main(int argc, char* argv[])
{
	char **mat_1;
	char **mat_2;
	unsigned long long **prod;

	unsigned long long start_time = get_time();
	printf("Starting app at time: %llu\n", start_time);
	
	mat_1 = malloc(sizeof(char *) * DIM_LEN);
	mat_2 = malloc(sizeof(char *) * DIM_LEN);
	prod = malloc(sizeof(unsigned long long *) * DIM_LEN);

	unsigned long long atime = get_time();
	printf("Time spent in allocation: %llu\n", atime - start_time);

	int i;
	for(i = 0; i < DIM_LEN; i++)
	{
		mat_1[i] = malloc(sizeof(char) * DIM_LEN);
		mat_2[i] = malloc(sizeof(char) * DIM_LEN);
		prod[i] = malloc(sizeof(unsigned long long) * DIM_LEN);
	}

	init_mat(mat_1);
	init_mat(mat_2);
	unsigned long long itime = get_time();
	printf("Time spent in initialization: %llu\n", itime - atime);

	cal_prod(mat_1, mat_2, prod);
	unsigned long long ptime = get_time();

	printf("Time spent in multiplication: %llu\n", ptime - itime);

	printf("Total time spent in application: %llu\n", ptime - start_time);
	return 0;
}

void init_mat(char **mat)
{
	int i, j;
	for(i = 0; i < DIM_LEN; i++)
	{
		for(j = 0; j < DIM_LEN; j++)
		{
			mat[i][j] = (random() % 9) + 1;
		}
	}
}
void cal_prod(char **mat_1,
			  char **mat_2,
			  unsigned long long **prod)
{
	int i, j, k;
	for(i = 0; i < DIM_LEN; i++)
	{
		for(j = 0; j < DIM_LEN; j++)
		{
			prod[i][j] = 0;
			for(k = 0; k < DIM_LEN; k++)
			{
				prod[i][j] += (mat_1[i][k] * mat_2[k][j]);
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

void print_mat_llu(unsigned long long **mat)
{
	int i, j;
	for(i = 0; i < DIM_LEN; i++)
	{
		for(j = 0; j < DIM_LEN; j++)
		{
			printf("%llu ", mat[i][j]);
		}
		printf("\n");
	}
}

void print_mat_char(char **mat)
{
	int i, j;
	for(i = 0; i < DIM_LEN; i++)
	{
		for(j = 0; j < DIM_LEN; j++)
		{
			printf("%c ", mat[i][j]);
		}
		printf("\n");
	}
}

