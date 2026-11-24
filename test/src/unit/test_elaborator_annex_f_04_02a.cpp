#include <gtest/gtest.h>

#include "elaborator/checker_rewrite.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(CheckerRewrite, OutputFormalIsOutsideAlgorithm) {
  PortDecl in_formal;
  in_formal.direction = Direction::kInput;
  PortDecl out_formal;
  out_formal.direction = Direction::kOutput;
  EXPECT_TRUE(CheckerRegistry::AlgorithmAppliesToFormal(in_formal));
  EXPECT_FALSE(CheckerRegistry::AlgorithmAppliesToFormal(out_formal));
}

TEST(CheckerRewrite, InputAndOutputFormalsArePartitioned) {
  ModuleDecl decl;
  decl.decl_kind = ModuleDeclKind::kChecker;
  decl.name = "chk";
  PortDecl in_formal;
  in_formal.direction = Direction::kInput;
  PortDecl implicit_formal;
  implicit_formal.direction = Direction::kNone;
  PortDecl out_formal;
  out_formal.direction = Direction::kOutput;
  decl.ports = {in_formal, implicit_formal, out_formal};
  CheckerRegistry reg;
  reg.Register(&decl);

  EXPECT_EQ(reg.InputFormalCount(&decl), 2u);
  EXPECT_EQ(reg.OutputFormalCount(&decl), 1u);

  auto fc = reg.Flatten("chk", 2);
  EXPECT_EQ(fc.input_formal_count, 2u);
  EXPECT_EQ(fc.output_formal_count, 1u);
  EXPECT_TRUE(fc.legal);
}

TEST(CheckerRewrite, InputArgArityMismatchNotLegal) {
  ModuleDecl decl;
  decl.decl_kind = ModuleDeclKind::kChecker;
  decl.name = "chk";
  PortDecl in_formal;
  in_formal.direction = Direction::kInput;
  PortDecl out_formal;
  out_formal.direction = Direction::kOutput;
  decl.ports = {in_formal, out_formal};
  CheckerRegistry reg;
  reg.Register(&decl);

  auto fc = reg.Flatten("chk", 2);
  EXPECT_FALSE(fc.legal);
}

TEST(CheckerRewrite, CountsNestedCheckerInstances) {
  ModuleDecl leaf;
  leaf.decl_kind = ModuleDeclKind::kChecker;
  leaf.name = "leaf";

  ModuleItem inst;
  inst.kind = ModuleItemKind::kModuleInst;
  inst.inst_module = "leaf";
  inst.inst_name = "u1";

  ModuleDecl root;
  root.decl_kind = ModuleDeclKind::kChecker;
  root.name = "root";
  root.ports = {};
  root.items = {&inst};

  CheckerRegistry reg;
  reg.Register(&leaf);
  reg.Register(&root);

  EXPECT_EQ(reg.CheckerInstanceCount(&root), 1);
  auto fc = reg.Flatten("root", 0);
  EXPECT_EQ(fc.remaining_instances, 0);
}

TEST(CheckerRewrite, CountsMultipleNestedCheckerInstances) {
  ModuleDecl leaf_a;
  leaf_a.decl_kind = ModuleDeclKind::kChecker;
  leaf_a.name = "leaf_a";

  ModuleDecl leaf_b;
  leaf_b.decl_kind = ModuleDeclKind::kChecker;
  leaf_b.name = "leaf_b";

  ModuleItem inst_a;
  inst_a.kind = ModuleItemKind::kModuleInst;
  inst_a.inst_module = "leaf_a";
  inst_a.inst_name = "u1";

  ModuleItem inst_b;
  inst_b.kind = ModuleItemKind::kModuleInst;
  inst_b.inst_module = "leaf_b";
  inst_b.inst_name = "u2";

  ModuleDecl root;
  root.decl_kind = ModuleDeclKind::kChecker;
  root.name = "root";
  root.items = {&inst_a, &inst_b};

  CheckerRegistry reg;
  reg.Register(&leaf_a);
  reg.Register(&leaf_b);
  reg.Register(&root);

  EXPECT_EQ(reg.CheckerInstanceCount(&root), 2);
  auto fc = reg.Flatten("root", 0);
  EXPECT_EQ(fc.remaining_instances, 0);
}

TEST(CheckerRewrite, LegalFlattenAcceptedAsCheckerInstance) {
  ModuleDecl decl;
  decl.decl_kind = ModuleDeclKind::kChecker;
  decl.name = "chk";
  CheckerRegistry reg;
  reg.Register(&decl);

  auto fc = reg.Flatten("chk", 0);
  EXPECT_TRUE(fc.legal);
  EXPECT_EQ(fc.remaining_instances, 0);
  EXPECT_TRUE(CheckerRegistry::IsAcceptableAsCheckerInstance(fc));
}

TEST(CheckerRewrite, NonCheckerDeclIsNotRegistered) {
  ModuleDecl module;
  module.decl_kind = ModuleDeclKind::kModule;
  module.name = "m";
  CheckerRegistry reg;
  reg.Register(&module);
  EXPECT_EQ(reg.Find("m"), nullptr);
}

TEST(CheckerRewrite, NonCheckerInstanceIsNotCounted) {
  ModuleItem inst;
  inst.kind = ModuleItemKind::kModuleInst;
  inst.inst_module = "some_module";
  inst.inst_name = "u1";

  ModuleDecl root;
  root.decl_kind = ModuleDeclKind::kChecker;
  root.name = "root";
  root.items = {&inst};

  CheckerRegistry reg;
  reg.Register(&root);
  EXPECT_EQ(reg.CheckerInstanceCount(&root), 0);
}

TEST(CheckerRewrite, LeafCheckerHasNoInstances) {
  ModuleDecl leaf;
  leaf.decl_kind = ModuleDeclKind::kChecker;
  leaf.name = "leaf";
  CheckerRegistry reg;
  reg.Register(&leaf);
  EXPECT_EQ(reg.CheckerInstanceCount(&leaf), 0);
}

TEST(CheckerRewrite, IllegalFlattenNotAcceptedAsCheckerInstance) {
  CheckerRegistry reg;
  auto fc = reg.Flatten("missing", 0);
  EXPECT_FALSE(fc.legal);
  EXPECT_FALSE(CheckerRegistry::IsAcceptableAsCheckerInstance(fc));
}

TEST(CheckerRewrite, NonOutputFormalStaysInsideAlgorithm) {
  PortDecl inout_formal;
  inout_formal.direction = Direction::kInout;
  EXPECT_TRUE(CheckerRegistry::AlgorithmAppliesToFormal(inout_formal));
}

}  // namespace
