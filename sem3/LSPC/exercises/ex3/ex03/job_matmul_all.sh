#!/bin/bash
#BSUB -J MATMUL_ALL
#BSUB -u your_email@tu-darmstadt.de
#BSUB -N
#BSUB -o MATMUL_ALL.%J.out
#BSUB -e MATMUL_ALL.%J.out
#BSUB -n 64
#BSUB -M 1024
#BSUB -a openmpi
#BSUB -W 00:15
#BSUB -q kurs1

module load gcc intel openmpi/intel

cd directory_where_the_executable_is

echo "--- SEQ ---"
./matmul_seq

for NP in 2 4 8 16 32 64
do
	echo "--- MPI $NP ---"
	mpiexec -np $NP ./matmul_mpi
	echo "--- TRANS $NP ---"
	mpiexec -np $NP ./matmul_trans
	echo "--- CONT $NP ---"
	mpiexec -np $NP ./matmul_cont
done

