#pragma once

#include <filesystem>
#include <string_view>

namespace delta {

class Arena;
class DiagEngine;
class SourceManager;
struct CompilationUnit;

class PrecompiledLibrary {
 public:
  static bool Save(std::string_view source, std::string_view library,
                   const std::filesystem::path& path);

  static bool Load(const std::filesystem::path& path, CompilationUnit& target,
                   SourceManager& mgr, Arena& arena, DiagEngine& diag);
};

}  // namespace delta
