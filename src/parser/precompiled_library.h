#pragma once

#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "preprocessor/protect_license.h"

namespace delta {

class Arena;
class DiagEngine;
class SourceManager;
struct CompilationUnit;

struct PrecompiledViewport {
  std::string object;
  std::string access;
  uint32_t line = 0;
  uint32_t first_line = 0;
  uint32_t last_line = 0;
};

struct PrecompiledDirectives {
  std::vector<ModuleDirectives> modules;
  std::vector<std::string> cell_modules;
  std::vector<ProtectLicense> runtime_licenses;
  std::vector<uint32_t> protected_lines;
  std::vector<PrecompiledViewport> viewports;
};

class PrecompiledLibrary {
 public:
  static bool Save(std::string_view source, std::string_view library,
                   const std::filesystem::path& path,
                   const PrecompiledDirectives& directives = {});

  static std::vector<std::string> CellNames(std::string_view source);

  static bool Load(const std::filesystem::path& path, CompilationUnit& target,
                   SourceManager& mgr, Arena& arena, DiagEngine& diag);

  static std::vector<ProtectLicense> RuntimeLicenses(
      const std::filesystem::path& path);
};

}  // namespace delta
