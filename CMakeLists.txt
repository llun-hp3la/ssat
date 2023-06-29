cmake_minimum_required(VERSION 3.11.4)

# C compiler on the system will be used
project (ssat C)

find_package(MPI REQUIRED)

# for C++ code
set(CMAKE_CXX_STANDARD 17)

add_executable(ssat src/main.c)
