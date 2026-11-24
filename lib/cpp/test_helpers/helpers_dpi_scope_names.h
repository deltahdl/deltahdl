#pragma once

#include <gtest/gtest.h>

#include <map>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "simulator/svdpi.h"

inline std::vector<std::string>& ScopeNamesSeenInC() {
  static std::vector<std::string> names;
  return names;
}

inline int SeeScopeName() {
  const char* name = svGetNameFromScope(svGetScope());
  ScopeNamesSeenInC().emplace_back(name == nullptr ? "" : name);
  return 0;
}

inline void RunDesignWithC(const std::string& src, SimFixture& f,
                           const std::map<std::string, void*>& functions,
                           const std::string& dir_name) {
  SeenInC().clear();
  ScopeNamesSeenInC().clear();
  RunWithImportsBound(src, f, functions, dir_name);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

inline std::vector<std::string> ScopeNamesOfRun(const std::string& src,
                                                const std::string& dir_name) {
  SimFixture f;
  RunDesignWithC(src, f, {{"see_scope", CAddress(&SeeScopeName)}}, dir_name);
  return ScopeNamesSeenInC();
}
