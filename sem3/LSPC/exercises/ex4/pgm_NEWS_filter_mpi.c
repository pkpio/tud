#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <mpi.h>
#include <time.h>

void write_pgm_file(const char *file_name, int width, int height, int *buf);
void read_pgm_data(FILE *fh, int width, int height, int *buf);
FILE* read_pgm_header(char *file_name, int *width, int *height, int *max_color);

void get_boundaries_from_neighbors(int* img_buf, int width, int proc_size);

void apply_NEWS_filter(int width, int height, int *original, int *cleaned);
int find_median(int count, int *vals);

unsigned long long get_time();

int my_rank;
int comm_size;

int main(int argc, char* argv[])
{
	if(argc != 3)
	{
		printf("Usage: ./app_name [input_file] [output_file]\n");
		return -1;
	}

	char file_name[128];
	char output_file[128];
	int flag;

	strcpy(file_name, argv[1]);
	strcpy(output_file, argv[2]);
	flag = atoi(argv[3]);

	MPI_Init(&argc, &argv);
	MPI_Comm_rank(MPI_COMM_WORLD, &my_rank);
	MPI_Comm_size(MPI_COMM_WORLD, &comm_size);

	int width, height, max_color;
	FILE* fh;
	int *data_buf, *out_buf, *img_buf, *final_buf;
	int proc_size, final_offset;

	unsigned long long start_time, end_time;

	if(my_rank == 0)
	{
		start_time = get_time();
		fh = read_pgm_header(file_name, &width, &height, &max_color);
		if(fh == NULL)
		{
			exit(-1);
		}
	
		data_buf = malloc(sizeof(int) * (width) * (height));
		read_pgm_data(fh, width, height, data_buf);
		fclose(fh);
	}
	

	MPI_Bcast(&width, 1, MPI_INT, 0, MPI_COMM_WORLD);
	MPI_Bcast(&height, 1, MPI_INT, 0, MPI_COMM_WORLD);
	MPI_Bcast(&max_color, 1, MPI_INT, 0, MPI_COMM_WORLD);

	proc_size = height * width / comm_size;

	int img_buf_size = proc_size;

	if(my_rank > 0)
	{
		img_buf_size = img_buf_size + width;
	}
	if(my_rank < comm_size - 1)
	{
		img_buf_size = img_buf_size + width;
	}

	img_buf = malloc(sizeof(int) * img_buf_size);

	int *input_buf = img_buf;
	if(my_rank > 0)
	{
		input_buf = &(img_buf[width]);
	}


	MPI_Scatter(data_buf, proc_size, MPI_INT, input_buf, proc_size, MPI_INT, 0, MPI_COMM_WORLD);

	get_boundaries_from_neighbors(img_buf, width, proc_size);

	out_buf = malloc(sizeof(int) * img_buf_size);
	apply_NEWS_filter(width, img_buf_size / width, img_buf, out_buf);

	if(my_rank == 0)
	{
		final_buf = malloc(sizeof(int) * width * height);
		final_offset = 0;
	}
	else
	{
		final_offset = width;
	}

	MPI_Gather(&(out_buf[final_offset]), proc_size, MPI_INT, final_buf, proc_size, MPI_INT, 0, MPI_COMM_WORLD);

	if(my_rank == 0)
	{
		write_pgm_file(output_file, width, height, final_buf);
	}

	free(out_buf);
	free(img_buf);
	if(my_rank == 0)
	{
		free(final_buf);
		free(data_buf);
		end_time = get_time();

		printf("Total time spent: %llu\n", end_time - start_time);
	}

	MPI_Finalize();
	return 0;
}

void get_boundaries_from_neighbors(int* img_buf, int width, int proc_size)
{
	MPI_Status stat;
	int bottom_offset = proc_size;
	int top_offset = width;

	//Update the top row, by getting the bottom row of process my_rank - 1
	if(my_rank > 0)
	{
		MPI_Recv(img_buf, width, MPI_INT, my_rank - 1, 0, MPI_COMM_WORLD, &stat);
	}
	else
	{
		bottom_offset = proc_size - width;
	}
	
	if(my_rank < comm_size - 1)
	{
		MPI_Send(&(img_buf[bottom_offset]), width, MPI_INT, my_rank + 1, 0, MPI_COMM_WORLD);
	}

	//Update the bottom row, by getting the top row of process my_rank + 1
	if(my_rank > 0)
	{
		MPI_Send(&(img_buf[top_offset]), width, MPI_INT, my_rank - 1, 0, MPI_COMM_WORLD);
	}

	if(my_rank < comm_size - 1)
	{
		MPI_Recv(&(img_buf[bottom_offset + width]), width, MPI_INT, my_rank + 1, 0, MPI_COMM_WORLD, &stat);
	}
}

void apply_NEWS_filter(int width, int height, int *original, int *cleaned)
{
	int i, j, ind;
	int orig_vals[5];
	for(i = 0; i < height; i++)
	{
		for(j = 0; j < width; j++)
		{
			ind = 0;
			orig_vals[ind++] = original[i * width + j];
			if(i > 0) //North, if there is any
			{
				orig_vals[ind++] = original[(i - 1) * width + j];
			}
			if(j < width) //East, if there is any
			{
				orig_vals[ind++] = original[(i) * width + j + 1];
			}
			if(j > 0) //West, if there is any
			{
				orig_vals[ind++] = original[(i) * width + j - 1];
			}
			if(i < height) //South, if there is any
			{
				orig_vals[ind++] = original[(i + 1) * width + j];
			}

			cleaned[i * width + j] = find_median(ind, orig_vals);
		}
	}
}

int find_median(int count, int *vals)
{
	int i, j, min_ind, tmp;
	//First, sort the values
	for(i = 0; i < count - 1; i++)
	{
		min_ind = i;
		for(j = i + 1; j < count; j++)
		{
			if(vals[min_ind] > vals[j])
			{
				min_ind = j;
			}
		}
		tmp = vals[min_ind];
		vals[min_ind] = vals[i];
		vals[i] = tmp;
	}

	//Now find median
	int half_ind = count / 2;
	if(count % 2 == 1)
	{
		return vals[half_ind];
	}
	return (vals[half_ind] + vals[half_ind - 1]) / 2;
}

void write_pgm_file(const char *file_name, int width, int height, int *buf)
{
	FILE *fh = fopen(file_name, "w");
	fprintf(fh, "P2\n");
	fprintf(fh, "# TMP file written by PGM reader/writer\n");
	fprintf(fh, "%d %d\n", width, height);

	int i, j;
	int max_val = 0;

	for(i = 0; i < height; i++)
	{
		for(j = 0; j < width; j++)
		{
			if(max_val < buf[i * (width) + j])
			{
				max_val = buf[i * (width) + j];
			}
		}
	}

	fprintf(fh, "%d\n", max_val);

	int ind = 0;
	for(i = 0; i < height; i++)
	{
		for(j = 0; j < width; j++)
		{
			fprintf(fh, "%d", buf[i * (width) + j]);
			ind++;
			if(ind % 12 == 0 || j == width || ind == (height * width ))
			{
				fprintf(fh, "\n");
			}
			else
			{
				fprintf(fh, " ");
			}
		}
	}

	fclose(fh);
}

void read_pgm_data(FILE *fh, int width, int height, int *buf)
{
	int i, j;
	for(i = 0; i < height; i++)
	{
		for(j = 0; j < width; j++)
		{
			fscanf(fh, "%d", &buf[i * (width) + j]);
		}
	}
}

FILE* read_pgm_header(char *file_name, int *width, int *height, int *max_color)
{
	int size = 255;
	char tmp[8];
	int data_read = 0;
	char line[size];
	char *pline = line;
	FILE *fh;
	int flag = 0;

	fh = fopen(file_name, "r");
	line[0] = '\n';
	while(flag != 4)
	{
			fgets(line, size, fh);
			pline = line;
		if(line[0] == '#')
		{
			continue;
		}
		while(sscanf(pline, "%s%n", tmp, &data_read) != EOF)
		{
			pline = pline + data_read;
			if(flag == 0)
			{
				if(strcmp("P2", tmp) != 0)
				{
					printf("Error reading file\n");
					return NULL;
				}
			}
			if(flag == 1)
			{
				*width = atoi(tmp);
			}
			if(flag == 2)
			{
				*height = atoi(tmp);
			}
			if(flag == 3)
			{
				*max_color = atoi(tmp);
			}
			flag++;
		}
	}
	return fh;
}

unsigned long long get_time()
{
	struct timespec ctime; 
	clock_gettime(CLOCK_REALTIME, &ctime);
	unsigned long long time = ctime.tv_sec * 1e9 + ctime.tv_nsec;
	return time;
}

