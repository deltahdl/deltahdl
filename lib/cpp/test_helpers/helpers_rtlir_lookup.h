#pragma once

#include <cstddef>
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

// How many elaborated variables in `mod` have a name ending in `suffix`, used
// to observe a loop generate construct without depending on how the elaborator
// spells a per-iteration name.
inline size_t CountVarsEndingIn(RtlirDesign* design, std::string_view mod,
                                std::string_view suffix) {
  size_t n = 0;
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return n;
  for (const auto& var : m->variables) {
    if (var.name.size() >= suffix.size() &&
        var.name.substr(var.name.size() - suffix.size()) == suffix) {
      ++n;
    }
  }
  return n;
}

// Whether `mod` holds at least one elaborated process of `kind`. A test that
// checks a procedural construct reached the design asks this rather than
// naming the process, since a process carries no name of its own.
inline bool HasProcess(RtlirDesign* design, std::string_view mod,
                       RtlirProcessKind kind) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return false;
  for (const auto& p : m->processes) {
    if (p.kind == kind) return true;
  }
  return false;
}
