#include "elaborator/property_rewrite.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §F.4.1: if flattened is not legal, source is not legal — unknown names
// surface that as legal=false.
TEST(PropertyRewrite, UnknownNameNotLegal) {
  PropertyRegistry reg;
  auto fp = reg.Flatten("missing", 0);
  EXPECT_FALSE(fp.legal);
}

// §F.4.1 step 2 substitutes callees; nested disable iff counts accumulate.
TEST(PropertyRewrite, NestedInstancesAccumulateDisableIff) {
  PropertyRegistry reg;

  ModuleItem leaf;
  leaf.kind = ModuleItemKind::kPropertyDecl;
  leaf.name = "leaf";
  leaf.prop_disable_iff_count = 1;
  reg.Register(&leaf);

  ModuleItem root;
  root.kind = ModuleItemKind::kPropertyDecl;
  root.name = "root";
  root.prop_disable_iff_count = 1;
  root.prop_instance_refs = {"leaf"};
  reg.Register(&root);

  auto fp = reg.Flatten("root", 0);
  EXPECT_EQ(fp.disable_iff_count, 2);
  EXPECT_FALSE(fp.legal);
}

// §F.4.1: a rewritten property may be the top-level property of a
// concurrent assertion, and the flattened form has no remaining instances.
TEST(PropertyRewrite, LegalFlattenAcceptsAsTopLevel) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  reg.Register(&decl);

  auto fp = reg.Flatten("p", 0);
  EXPECT_TRUE(fp.legal);
  EXPECT_EQ(fp.remaining_instances, 0);
  EXPECT_TRUE(PropertyRegistry::IsAcceptableAsTopLevelConcurrent(fp));
}

// §F.4.1 step 2: actual count must bind every formal.
TEST(PropertyRewrite, ArgArityMismatchSurfacesAsNotLegal) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  decl.prop_formals = {"a", "b", "c"};
  reg.Register(&decl);

  EXPECT_FALSE(reg.Flatten("p", 0).legal);
  EXPECT_FALSE(reg.Flatten("p", 2).legal);
  EXPECT_TRUE(reg.Flatten("p", 3).legal);
}

}  // namespace
