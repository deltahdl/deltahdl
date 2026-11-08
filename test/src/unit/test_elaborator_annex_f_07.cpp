#include <gtest/gtest.h>

#include "elaborator/property_rewrite.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(RecursivePropertyDependencyDigraph,
     RecursiveIffInStronglyConnectedComponent) {
  PropertyRegistry reg;
  ModuleItem p1;
  p1.kind = ModuleItemKind::kPropertyDecl;
  p1.name = "p1";
  p1.prop_instance_refs = {"p2", "p3"};
  ModuleItem p2;
  p2.kind = ModuleItemKind::kPropertyDecl;
  p2.name = "p2";
  ModuleItem p3;
  p3.kind = ModuleItemKind::kPropertyDecl;
  p3.name = "p3";
  p3.prop_instance_refs = {"p1"};
  reg.Register(&p1);
  reg.Register(&p2);
  reg.Register(&p3);

  EXPECT_TRUE(reg.IsRecursiveProperty(&p1));
  EXPECT_TRUE(reg.IsRecursiveProperty(&p3));
  EXPECT_FALSE(reg.IsRecursiveProperty(&p2));
}

TEST(RecursivePropertyDependencyDigraph,
     ReachabilityToRecursivePropertyIsTransitive) {
  PropertyRegistry reg;
  ModuleItem rec;
  rec.kind = ModuleItemKind::kPropertyDecl;
  rec.name = "rec";
  rec.prop_instance_refs = {"rec"};
  ModuleItem mid;
  mid.kind = ModuleItemKind::kPropertyDecl;
  mid.name = "mid";
  mid.prop_instance_refs = {"rec"};
  ModuleItem unrelated;
  unrelated.kind = ModuleItemKind::kPropertyDecl;
  unrelated.name = "unrelated";
  reg.Register(&rec);
  reg.Register(&mid);
  reg.Register(&unrelated);

  EXPECT_FALSE(reg.IsRecursiveProperty(&mid));
  EXPECT_TRUE(reg.ReachesRecursiveProperty(&mid));
  EXPECT_FALSE(reg.ReachesRecursiveProperty(&unrelated));
}

TEST(RecursivePropertyRestrictionEnforcement,
     NotOnPropertyReachingRecursiveRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "  property mid(p);\n"
      "    rec(p);\n"
      "  endproperty\n"
      "  property bad(p);\n"
      "    not mid(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "negation or strong operator applied to property \"mid\"",
                    8, "16.12.17"));
}

TEST(RecursivePropertyRestrictionEnforcement,
     DisableIffInRecursivePropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module m(input logic rst);\n"
      "  property rec(p);\n"
      "    disable iff (rst)\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "recursive property \"rec\" may not use disable iff (Restriction 2)", 2,
      "16.12.17"));
}

TEST(RecursivePropertyRestrictionEnforcement, ZeroWeightSelfCycleRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |-> rec(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "recursive property \"rec\" lies on a recursion "
                            "cycle with no positive advance in time",
                            2, "16.12.17"));
}

TEST(RecursivePropertyRestrictionEnforcement, PositiveWeightSelfCycleAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property rec(p);\n"
      "    p and (1'b1 |=> rec(p));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecursivePropertyRestrictionEnforcement, ZeroWeightMutualCycleRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property a(p);\n"
      "    p and b(p);\n"
      "  endproperty\n"
      "  property b(p);\n"
      "    p and a(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "recursive property \"a\" lies on a recursion "
                            "cycle with no positive advance in time",
                            2, "16.12.17"));
}

TEST(RecursivePropertyRestrictionEnforcement,
     PositiveWeightMutualCycleAllowed) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property a(p);\n"
      "    p and (1'b1 |=> b(p));\n"
      "  endproperty\n"
      "  property b(p);\n"
      "    p and a(p);\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecursivePropertyRestrictionEnforcement,
     RecursiveArgumentToNonLocalFormalRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  property fib (int a, b, n, fib_sig);\n"
      "    (n > 0) |->\n"
      "    ((fib_sig == a) and (1'b1 |=> fib(b, a + b, n - 1, fib_sig)));\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "recursive instance of \"fib\" passes an actual "
                            "argument that contains a formal of \"fib\"",
                            2, "16.12.17"));
}

}  // namespace
