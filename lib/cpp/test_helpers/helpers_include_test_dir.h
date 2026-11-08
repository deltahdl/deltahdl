#pragma once

#include <unistd.h>

#include <filesystem>
#include <fstream>
#include <string>

struct IncludeTestDir {
  std::filesystem::path dir;
  IncludeTestDir() {
    dir = std::filesystem::temp_directory_path() /
          ("delta_test_" + std::to_string(getpid()));
    std::filesystem::create_directories(dir);
  }
  ~IncludeTestDir() { std::filesystem::remove_all(dir); }
  std::filesystem::path WriteFile(const std::string& rel,
                                  const std::string& content) {
    auto full = dir / rel;
    std::filesystem::create_directories(full.parent_path());
    std::ofstream ofs(full);
    ofs << content;
    return full;
  }
};
