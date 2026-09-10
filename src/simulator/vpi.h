#pragma once

// The repository's own spelling of the VPI interface, and the one every
// translation unit under src/ that reaches the VPI is written against. What it
// provides is simulator/vpi_user.h, which holds the sub-headers in dependency
// order and which §36.7 names as the file a PLI application includes; the two
// names stand for one interface today because every declaration an application
// needs is one this tool's own code needs too.

#include "simulator/vpi_user.h"
