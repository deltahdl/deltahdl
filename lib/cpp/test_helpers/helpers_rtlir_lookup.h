#pragma once

#include <string_view>

#include "elaborator/rtlir.h"

// Lookups into an elaborated design, for a test that names the thing it wants
// to inspect rather than walking the design to reach it. Each returns nullptr
// when the name is not found, so a test can assert on absence as well.

using namespace delta;

inline const RtlirModule* FindModule(RtlirDesign* design,
                                     std::string_view name) {
  auto it = design->all_modules.find(name);
  return it == design->all_modules.end() ? nullptr : it->second;
}

inline const RtlirVariable* FindVar(RtlirDesign* design, std::string_view mod,
                                    std::string_view name) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return nullptr;
  for (const auto& var : m->variables) {
    if (var.name == name) return &var;
  }
  return nullptr;
}

inline const RtlirNet* FindNet(RtlirDesign* design, std::string_view mod,
                               std::string_view name) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return nullptr;
  for (const auto& net : m->nets) {
    if (net.name == name) return &net;
  }
  return nullptr;
}

inline const RtlirParamDecl* FindParam(RtlirDesign* design,
                                       std::string_view mod,
                                       std::string_view name) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return nullptr;
  for (const auto& p : m->params) {
    if (p.name == name) return &p;
  }
  return nullptr;
}
