# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.22

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/obhalerao/cornell/cs6120/btor2i/btor2tools-sys/btor2tools

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/obhalerao/cornell/cs6120/btor2i/build

# Include any dependencies generated for this target.
include src/CMakeFiles/btorsplit.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include src/CMakeFiles/btorsplit.dir/compiler_depend.make

# Include the progress variables for this target.
include src/CMakeFiles/btorsplit.dir/progress.make

# Include the compile flags for this target's objects.
include src/CMakeFiles/btorsplit.dir/flags.make

src/CMakeFiles/btorsplit.dir/btorsplit.cpp.o: src/CMakeFiles/btorsplit.dir/flags.make
src/CMakeFiles/btorsplit.dir/btorsplit.cpp.o: /home/obhalerao/cornell/cs6120/btor2i/btor2tools-sys/btor2tools/src/btorsplit.cpp
src/CMakeFiles/btorsplit.dir/btorsplit.cpp.o: src/CMakeFiles/btorsplit.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/obhalerao/cornell/cs6120/btor2i/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object src/CMakeFiles/btorsplit.dir/btorsplit.cpp.o"
	cd /home/obhalerao/cornell/cs6120/btor2i/build/src && /usr/bin/g++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT src/CMakeFiles/btorsplit.dir/btorsplit.cpp.o -MF CMakeFiles/btorsplit.dir/btorsplit.cpp.o.d -o CMakeFiles/btorsplit.dir/btorsplit.cpp.o -c /home/obhalerao/cornell/cs6120/btor2i/btor2tools-sys/btor2tools/src/btorsplit.cpp

src/CMakeFiles/btorsplit.dir/btorsplit.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/btorsplit.dir/btorsplit.cpp.i"
	cd /home/obhalerao/cornell/cs6120/btor2i/build/src && /usr/bin/g++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/obhalerao/cornell/cs6120/btor2i/btor2tools-sys/btor2tools/src/btorsplit.cpp > CMakeFiles/btorsplit.dir/btorsplit.cpp.i

src/CMakeFiles/btorsplit.dir/btorsplit.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/btorsplit.dir/btorsplit.cpp.s"
	cd /home/obhalerao/cornell/cs6120/btor2i/build/src && /usr/bin/g++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/obhalerao/cornell/cs6120/btor2i/btor2tools-sys/btor2tools/src/btorsplit.cpp -o CMakeFiles/btorsplit.dir/btorsplit.cpp.s

# Object files for target btorsplit
btorsplit_OBJECTS = \
"CMakeFiles/btorsplit.dir/btorsplit.cpp.o"

# External object files for target btorsplit
btorsplit_EXTERNAL_OBJECTS =

bin/btorsplit: src/CMakeFiles/btorsplit.dir/btorsplit.cpp.o
bin/btorsplit: src/CMakeFiles/btorsplit.dir/build.make
bin/btorsplit: src/CMakeFiles/btorsplit.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/obhalerao/cornell/cs6120/btor2i/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable ../bin/btorsplit"
	cd /home/obhalerao/cornell/cs6120/btor2i/build/src && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/btorsplit.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
src/CMakeFiles/btorsplit.dir/build: bin/btorsplit
.PHONY : src/CMakeFiles/btorsplit.dir/build

src/CMakeFiles/btorsplit.dir/clean:
	cd /home/obhalerao/cornell/cs6120/btor2i/build/src && $(CMAKE_COMMAND) -P CMakeFiles/btorsplit.dir/cmake_clean.cmake
.PHONY : src/CMakeFiles/btorsplit.dir/clean

src/CMakeFiles/btorsplit.dir/depend:
	cd /home/obhalerao/cornell/cs6120/btor2i/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/obhalerao/cornell/cs6120/btor2i/btor2tools-sys/btor2tools /home/obhalerao/cornell/cs6120/btor2i/btor2tools-sys/btor2tools/src /home/obhalerao/cornell/cs6120/btor2i/build /home/obhalerao/cornell/cs6120/btor2i/build/src /home/obhalerao/cornell/cs6120/btor2i/build/src/CMakeFiles/btorsplit.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/CMakeFiles/btorsplit.dir/depend
