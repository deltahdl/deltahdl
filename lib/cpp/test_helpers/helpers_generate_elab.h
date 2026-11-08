#pragma once

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/parser.h"

using namespace delta;

struct GenerateElab {
  ElabFixture f;
  CompilationUnit* cu = nullptr;
  RtlirDesign* design = nullptr;
};

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
  r.f.has_errors.Record(src);
  return r;
}

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
