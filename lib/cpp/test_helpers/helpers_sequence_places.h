#pragma once

#include <string>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

inline std::string InEverySequencePlace(const std::string& body) {
  return "module m;\n"
         "  sequence s; " +
         body +
         "; endsequence\n"
         "  property q; " +
         body +
         "; endproperty\n"
         "  assert property (" +
         body +
         ");\n"
         "endmodule\n"
         "package p;\n"
         "  sequence s; " +
         body +
         "; endsequence\n"
         "endpackage\n";
}

inline const delta::SeqLinearBody* TreeSequenceBody(
    const delta::PropertyExprNode* tree) {
  if (tree == nullptr || tree->sequence == nullptr) return nullptr;
  return &tree->sequence->seq_linear;
}

inline const delta::SeqLinearBody* AssertionSequenceBody(
    const delta::Stmt* stmt) {
  if (stmt == nullptr) return nullptr;
  if (stmt->assert_sequence != nullptr) {
    return &stmt->assert_sequence->seq_linear;
  }
  return TreeSequenceBody(stmt->assert_property);
}

inline std::vector<const delta::SeqLinearBody*> SequenceBodiesInEveryPlace(
    const ParseResult& r) {
  using delta::ModuleItem;
  using delta::ModuleItemKind;
  std::vector<const delta::SeqLinearBody*> out;
  const auto& items = r.cu->modules[0]->items;
  const ModuleItem* seq = FindItemByKind(items, ModuleItemKind::kSequenceDecl);
  out.push_back(seq == nullptr ? nullptr : &seq->seq_linear);
  const ModuleItem* prop = FindItemByKind(items, ModuleItemKind::kPropertyDecl);
  out.push_back(prop == nullptr ? nullptr
                                : TreeSequenceBody(prop->prop_body_tree));
  const ModuleItem* assertion =
      FindItemByKind(items, ModuleItemKind::kAssertProperty);
  out.push_back(assertion == nullptr ? nullptr
                                     : AssertionSequenceBody(assertion->body));
  const ModuleItem* packaged =
      FindItemByKind(r.cu->packages[0]->items, ModuleItemKind::kSequenceDecl);
  out.push_back(packaged == nullptr ? nullptr : &packaged->seq_linear);
  return out;
}
