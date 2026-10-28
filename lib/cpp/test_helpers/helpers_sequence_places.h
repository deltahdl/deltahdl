#pragma once

#include <string>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

// The source writing the sequence_expr `body` in each place §16.8, §16.12
// and §16.14 let one stand: a sequence a module declares, a property it
// declares, an assertion it holds and a sequence a package declares.
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

// The sequence a property tree stands for, where its root is one.
inline const delta::SeqLinearBody* TreeSequenceBody(
    const delta::PropertyExprNode* tree) {
  if (tree == nullptr || tree->sequence == nullptr) return nullptr;
  return &tree->sequence->seq_linear;
}

// The sequence an assertion statement stands for: the one it carries alone,
// or, where its operands name clocks of their own and it is carried as a
// tree, the tree's.
inline const delta::SeqLinearBody* AssertionSequenceBody(
    const delta::Stmt* stmt) {
  if (stmt == nullptr) return nullptr;
  if (stmt->assert_sequence != nullptr) {
    return &stmt->assert_sequence->seq_linear;
  }
  return TreeSequenceBody(stmt->assert_property);
}

// The linear forms InEverySequencePlace's four places were read into, in its
// order; null for a place that holds none.
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
