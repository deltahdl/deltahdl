// §3.12.1 (printed page 56): with --compilation-unit-per-file a compilation-unit
// declaration left open at the end of a file carries its unit into the next
// file, where it completes. The struct typedef opens here and closes in
// next.sv, whose module declares a variable of the completed type and prints
// the member it sets.
typedef struct {
  int a;
