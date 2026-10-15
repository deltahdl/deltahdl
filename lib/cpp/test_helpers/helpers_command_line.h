#pragma once

#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>
#include <vector>

#include "driver/cli_options.h"

// One reading of a command line for a test whose subject is what the driver
// makes of a switch. ParseArgs starts at index 1 because argv[0] is the
// program name, so the program name is prepended here and no case writes it.
// The words are copied into buffers this function owns because ParseArgs takes
// a non-const `char* argv[]`.

// Runs ParseArgs over `args`, the arguments as written on the command line,
// filling `opts` and answering whether the parse was accepted.
inline bool ParseCommandLine(const std::vector<std::string>& args,
                             delta::CliOptions& opts) {
  std::vector<std::string> words;
  words.reserve(args.size() + 1);
  words.emplace_back("deltahdl");
  for (const std::string& arg : args) words.push_back(arg);
  std::vector<char*> argv;
  argv.reserve(words.size());
  for (std::string& word : words) argv.push_back(word.data());
  return delta::ParseArgs(static_cast<int>(argv.size()), argv.data(), opts);
}

// The same, with what ParseArgs prints to std::cerr captured into `err` instead
// of shown, for a case whose subject is the report a switch draws.
inline bool ParseCommandLineCapturingStderr(
    const std::vector<std::string>& args, delta::CliOptions& opts,
    std::string& err) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cerr.rdbuf(captured.rdbuf());
  bool ok = ParseCommandLine(args, opts);
  std::cerr.rdbuf(old_buf);
  err = captured.str();
  return ok;
}
