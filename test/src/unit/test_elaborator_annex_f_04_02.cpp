#include <gtest/gtest.h>

#include "elaborator/checker_rewrite.h"

using namespace delta;

namespace {

// §F.4.2: checker formal arguments with output direction are treated
// differently (see §17.2); the rewriting algorithm does not apply to them.
TEST(CheckerRewrite, OutputFormalIsOutsideAlgorithm) {
  PortDecl in_formal;
  in_formal.direction = Direction::kInput;
  PortDecl out_formal;
  out_formal.direction = Direction::kOutput;
  EXPECT_TRUE(CheckerRegistry::AlgorithmAppliesToFormal(in_formal));
  EXPECT_FALSE(CheckerRegistry::AlgorithmAppliesToFormal(out_formal));
}

// §F.4.2: only formal input arguments receive substituted actuals, so the
// flatten model counts input formals separately from the output formals it
// leaves untouched.
TEST(CheckerRewrite, InputAndOutputFormalsArePartitioned) {
  ModuleDecl decl;
  decl.decl_kind = ModuleDeclKind::kChecker;
  decl.name = "chk";
  PortDecl in_formal;
  in_formal.direction = Direction::kInput;
  PortDecl implicit_formal;  // no explicit direction defaults to input-like
  implicit_formal.direction = Direction::kNone;
  PortDecl out_formal;
  out_formal.direction = Direction::kOutput;
  decl.ports = {in_formal, implicit_formal, out_formal};
  CheckerRegistry reg;
  reg.Register(&decl);

  EXPECT_EQ(reg.InputFormalCount(&decl), 2u);
  EXPECT_EQ(reg.OutputFormalCount(&decl), 1u);

  // Binding only the two input formals is legal; the output formal must not be
  // bound by the algorithm.
  auto fc = reg.Flatten("chk", 2);
  EXPECT_EQ(fc.input_formal_count, 2u);
  EXPECT_EQ(fc.output_formal_count, 1u);
  EXPECT_TRUE(fc.legal);
}

// §F.4.2: actuals are substituted for references to the formal input
// arguments, so the actual count must bind every input formal. A mismatch
// makes the flattened checker — and therefore the source — not legal.
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

  // Counting the output formal toward the actuals would over-supply the input
  // formals: only one input formal exists.
  auto fc = reg.Flatten("chk", 2);
  EXPECT_FALSE(fc.legal);
}

// §F.4.2: the algorithm targets checkers that contain one or more instances of
// other checkers; such checker instances are recognized in the body.
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
  // The flattened result is a checker without instances.
  auto fc = reg.Flatten("root", 0);
  EXPECT_EQ(fc.remaining_instances, 0);
}

// §F.4.2: the algorithm targets a checker containing "one or more" instances of
// other checkers, so a body holding several checker instances counts each one,
// and the flattened result still resolves to a checker without instances.
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

  // Both checker instances are recognized in the body.
  EXPECT_EQ(reg.CheckerInstanceCount(&root), 2);
  // However many instances the source held, the flattened checker has none.
  auto fc = reg.Flatten("root", 0);
  EXPECT_EQ(fc.remaining_instances, 0);
}

// §F.4.2: a rewritten checker may be a nested checker instance or a top-level
// checker instance; once legal and instance-free, either placement is
// acceptable.
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

// §F.4.2: only checker declarations are registered as flattenable sources.
TEST(CheckerRewrite, NonCheckerDeclIsNotRegistered) {
  ModuleDecl module;
  module.decl_kind = ModuleDeclKind::kModule;
  module.name = "m";
  CheckerRegistry reg;
  reg.Register(&module);
  EXPECT_EQ(reg.Find("m"), nullptr);
}

// §F.4.2: the algorithm targets instances of other checkers. An instance whose
// target is not a checker is not a checker instance and must not be counted.
TEST(CheckerRewrite, NonCheckerInstanceIsNotCounted) {
  ModuleItem inst;
  inst.kind = ModuleItemKind::kModuleInst;
  inst.inst_module = "some_module";  // not a registered checker
  inst.inst_name = "u1";

  ModuleDecl root;
  root.decl_kind = ModuleDeclKind::kChecker;
  root.name = "root";
  root.items = {&inst};

  CheckerRegistry reg;
  reg.Register(&root);
  EXPECT_EQ(reg.CheckerInstanceCount(&root), 0);
}

// §F.4.2: a checker that already contains no checker instances is its own
// flattened result — the instance count is zero.
TEST(CheckerRewrite, LeafCheckerHasNoInstances) {
  ModuleDecl leaf;
  leaf.decl_kind = ModuleDeclKind::kChecker;
  leaf.name = "leaf";
  CheckerRegistry reg;
  reg.Register(&leaf);
  EXPECT_EQ(reg.CheckerInstanceCount(&leaf), 0);
}

// §F.4.2: if the flattened checker is not legal, the source is not legal, so an
// illegal flattened checker is not acceptable as a checker instance anywhere.
TEST(CheckerRewrite, IllegalFlattenNotAcceptedAsCheckerInstance) {
  CheckerRegistry reg;
  auto fc = reg.Flatten("missing", 0);
  EXPECT_FALSE(fc.legal);
  EXPECT_FALSE(CheckerRegistry::IsAcceptableAsCheckerInstance(fc));
}

// §F.4.2: only output-direction formals are excluded from the algorithm; a
// formal with any other direction (e.g. inout) remains within the algorithm.
TEST(CheckerRewrite, NonOutputFormalStaysInsideAlgorithm) {
  PortDecl inout_formal;
  inout_formal.direction = Direction::kInout;
  EXPECT_TRUE(CheckerRegistry::AlgorithmAppliesToFormal(inout_formal));
}

}  // namespace
