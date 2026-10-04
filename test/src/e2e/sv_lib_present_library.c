/* Annex J.4: the shared library sv_lib_present_library.sv names with -sv_lib,
 * built beside the run by the e2e runner from this file. It defines one
 * function and calls nothing, so it loads whatever the tool provides. */
int sv_lib_present_library_marker(void) { return 1; }
