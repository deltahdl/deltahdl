#pragma once

#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>
#include <system_error>

struct ScratchDir {
  std::filesystem::path dir;

  ScratchDir() {
    static std::atomic<uint64_t> counter{0};
    auto seq = counter.fetch_add(1);
    dir = std::filesystem::temp_directory_path() /
          ("delta_scratch_" + std::to_string(::getpid()) + "_" +
           std::to_string(seq));
    std::filesystem::create_directories(dir);
    dir = std::filesystem::weakly_canonical(dir);
  }

  ~ScratchDir() {
    std::error_code ec;
    std::filesystem::remove_all(dir, ec);
  }

  ScratchDir(const ScratchDir&) = delete;
  ScratchDir& operator=(const ScratchDir&) = delete;

  std::filesystem::path Write(const std::string& rel,
                              const std::string& content) {
    auto full = dir / rel;
    std::filesystem::create_directories(full.parent_path());
    std::ofstream ofs(full);
    ofs << content;
    return full;
  }
};

struct ScratchWorkingDir : ScratchDir {
  std::filesystem::path entry = std::filesystem::current_path();

  ScratchWorkingDir() { std::filesystem::current_path(dir); }

  ~ScratchWorkingDir() {
    std::error_code ec;
    std::filesystem::current_path(entry, ec);
  }

  ScratchWorkingDir(const ScratchWorkingDir&) = delete;
  ScratchWorkingDir& operator=(const ScratchWorkingDir&) = delete;
};
