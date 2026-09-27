// A design with no top-level module has no instance for --vcd to root the dump
// at. The run still writes the file's header, and its definitions hold no scope
// and no variable.
typedef int vcd_option_word_t;
