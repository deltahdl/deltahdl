#pragma once

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"

using namespace delta;

// Bundles the elaboration fixture together with the CompilationUnit and the
// elaborated RtlirDesign so generate-construct tests can inspect both the
// parsed module items and the final design.
struct GenerateElab {
  ElabFixture f;
  CompilationUnit* cu = nullptr;
  RtlirDesign* design = nullptr;
};

// Parses and elaborates `src`, returning the fixture, CompilationUnit, and the
// resulting design. `top` selects the top module (defaults to the last module).
inline GenerateElab RunGenerateElaboration(const std::string& src,
                                           std::string_view top = "") {
  GenerateElab r;
  auto fid = r.f.mgr.AddFile("<test>", src);
  Lexer lexer(r.f.mgr.FileContent(fid), fid, r.f.diag);
  Parser parser(lexer, r.f.arena, r.f.diag);
  r.cu = parser.Parse();
  if (!r.cu) return r;
  auto name = top.empty() ? r.cu->modules.back()->name : top;
  Elaborator elab(r.f.arena, r.f.diag, r.cu);
  r.design = elab.Elaborate(name);
  r.f.has_errors.Record(r.f.diag.HasErrors(), src);
  return r;
}

// Checks the names carried by the first two generate-if constructs `mod`
// declares, in declaration order.
//
// A module that states a naming rule declares the two constructs the rule
// distinguishes among items that are not generate constructs at all, so the
// two are picked out by kind rather than by position.
inline void ExpectFirstTwoGenerateIfNames(const ModuleDecl& mod,
                                          std::string_view first_name,
                                          std::string_view second_name) {
  ModuleItem* first = nullptr;
  ModuleItem* second = nullptr;
  for (auto* it : mod.items) {
    if (it->kind != ModuleItemKind::kGenerateIf) continue;
    if (first == nullptr) {
      first = it;
    } else if (second == nullptr) {
      second = it;
    }
  }
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->name, first_name);
  EXPECT_EQ(second->name, second_name);
}
