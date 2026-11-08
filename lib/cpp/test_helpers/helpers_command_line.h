#pragma once

#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>
#include <vector>

#include "driver/cli_options.h"

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
