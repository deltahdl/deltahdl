// §38.37.2 ("Initializing VPI system task or system function callbacks"): the
// file this tool supplies containing the vlog_startup_routines array. "A tool
// vendor shall supply a file that contains the vlog_startup_routines array. The
// names of the PLI application register functions shall be added to this
// vendor-supplied file."
//
// §38.37.2 leaves two things to the tool vendor to define, and this is where
// they are defined for deltahdl.
//
// The location of vlog_startup_routines is this file,
// src/simulator/vlog_startup_routines.cpp.
//
// The procedure for linking vlog_startup_routines with the tool is to declare
// the PLI application's register function above the array and to add its name
// to the array ahead of the null terminator, then to build the tool with the
// application's own translation units listed beside this one in
// src/CMakeLists.txt. The register functions then run just after the simulator
// is invoked, which is where src/main.cpp walks this array.

#include "simulator/vpi_globals.h"

// §38.37.2: "A C function using the array definition shall be provided as
// follows: void (*vlog_startup_routines[]) ();" - a null-terminated static
// array of functions taking no arguments and returning nothing, which is what
// §36.9.1's VlogStartupRoutine names. The array is declared extern "C" so that
// a PLI application, whose register functions are C functions, links against
// the name the standard fixes rather than against a mangled one.
//
// §38.37.2: "Entries in the array shall be added by the user." The tool ships
// the array holding nothing but its terminator, so every routine that runs at
// startup is one somebody added here.
extern "C" {
delta::VlogStartupRoutine vlog_startup_routines[] = {
    nullptr,
};
}
