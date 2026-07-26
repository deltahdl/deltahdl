#pragma once

#include <unistd.h>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>
#include <system_error>

// A scratch directory that exists for as long as one test does, for a rule
// whose input is a file the tool has to read off disk rather than a string a
// test hands it.
//
// The name is unique per process and per instance, so tests that run
// concurrently do not write over each other. The path is canonicalized because
// a loader that anchors a relative path to a file's own directory canonicalizes
// first -- on macOS /var resolves to /private/var -- and a test asserting on
// paths has to see what the loader sees.
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

  // Writes `content` to `rel` under the directory, creating any intermediate
  // directories the relative path names, and returns the full path.
  std::filesystem::path Write(const std::string& rel,
                              const std::string& content) {
    auto full = dir / rel;
    std::filesystem::create_directories(full.parent_path());
    std::ofstream ofs(full);
    ofs << content;
    return full;
  }
};
