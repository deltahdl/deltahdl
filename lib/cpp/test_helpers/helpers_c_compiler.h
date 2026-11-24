#pragma once

#include <fcntl.h>
#include <gtest/gtest.h>
#include <spawn.h>
#include <sys/wait.h>

#include <algorithm>
#include <cctype>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

extern char** environ;

struct CompilerResult {
  bool succeeded = false;
  std::string output;
};

inline std::filesystem::path RepositoryRoot() {
  std::filesystem::path root(__FILE__);
  for (int level = 0; level < 4; ++level) root = root.parent_path();
  return root;
}

inline std::filesystem::path CompilerWorkDir() {
  std::string name = "compiler_run";
  if (const auto* test =
          ::testing::UnitTest::GetInstance()->current_test_info()) {
    name = std::string(test->test_suite_name()) + "." + test->name();
  }
  std::filesystem::path dir =
      std::filesystem::path(::testing::TempDir()) / name;
  std::filesystem::create_directories(dir);
  return dir;
}

inline bool SpawnedCommandSucceeds(std::vector<std::string> command,
                                   const std::string& log) {
  std::vector<char*> argv;
  argv.reserve(command.size() + 1);
  for (std::string& word : command) argv.push_back(word.data());
  argv.push_back(nullptr);
  posix_spawn_file_actions_t to_log = {};
  posix_spawn_file_actions_init(&to_log);
  posix_spawn_file_actions_addopen(&to_log, 1, log.c_str(), O_WRONLY | O_CREAT,
                                   0600);
  posix_spawn_file_actions_adddup2(&to_log, 1, 2);
  pid_t child = 0;
  int status = -1;
  int spawned =
      posix_spawnp(&child, argv[0], &to_log, nullptr, argv.data(), environ);
  posix_spawn_file_actions_destroy(&to_log);
  return spawned == 0 && waitpid(child, &status, 0) == child && status == 0;
}

inline CompilerResult CompileSource(const std::string& source,
                                    const std::vector<std::string>& flags) {
  std::filesystem::path dir = CompilerWorkDir();
  std::string input = (dir / "source.txt").string();
  std::string log = (dir / "output.txt").string();
  std::ofstream(input) << source;
  std::vector<std::string> command = {"cc"};
  command.insert(command.end(), flags.begin(), flags.end());
  command.insert(command.end(),
                 {"-I", (RepositoryRoot() / "src").string(), input});
  CompilerResult result;
  result.succeeded = SpawnedCommandSucceeds(command, log);
  std::ostringstream text;
  text << std::ifstream(log).rdbuf();
  result.output = text.str();
  std::filesystem::remove_all(dir);
  return result;
}

inline CompilerResult CompileAsC(const std::string& source) {
  return CompileSource(source,
                       {"-x", "c", "-std=c99", "-pedantic-errors", "-Werror",
                        "-Wno-shift-negative-value", "-fsyntax-only"});
}

inline CompilerResult CompileAsCxx(const std::string& source) {
  return CompileSource(source,
                       {"-x", "c++", "-std=c++17", "-Werror", "-fsyntax-only"});
}

inline std::string PreprocessedWithoutSpaces(const std::string& source,
                                             std::vector<std::string> flags) {
  std::filesystem::path stubs(CompilerWorkDir().string() + ".stubs");
  std::filesystem::create_directories(stubs / "sys");
  for (const char* header :
       {"stdint.h", "stdarg.h", "inttypes.h", "sys/types.h"}) {
    std::ofstream(stubs / header) << "\n";
  }
  flags.insert(flags.end(), {"-E", "-P", "-nostdinc", "-I", stubs.string()});
  CompilerResult run = CompileSource(source, flags);
  std::filesystem::remove_all(stubs);
  EXPECT_TRUE(run.succeeded) << run.output;
  std::string text = run.output;
  text.erase(std::remove_if(text.begin(), text.end(),
                            [](unsigned char c) { return std::isspace(c); }),
             text.end());
  return text;
}
