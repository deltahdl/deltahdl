#pragma once

#include <cstddef>
#include <string_view>

#include "elaborator/rtlir.h"

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

inline bool HasProcess(RtlirDesign* design, std::string_view mod,
                       RtlirProcessKind kind) {
  const auto* m = FindModule(design, mod);
  if (m == nullptr) return false;
  for (const auto& p : m->processes) {
    if (p.kind == kind) return true;
  }
  return false;
}
