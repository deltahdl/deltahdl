#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassConstraintElaboration, WeakReferenceDeclOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_obj) wr;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceAsMemberOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "class holder;\n"
             "  weak_reference #(my_obj) wr;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassTypeError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    weak_reference #(int) wr;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 3, "8.30.1"));
}

TEST(ClassConstraintElaboration, WeakReferenceAsFunctionArgOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  function void f(weak_reference #(my_obj) wr);\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassMemberError) {
  ElabFixture f;
  ElabOk(
      "class holder;\n"
      "  weak_reference #(int) wr;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 2, "8.30.1"));
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassFunctionArgError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  function void f(weak_reference #(int) wr);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 2, "8.30.1"));
}

TEST(ClassConstraintElaboration, WeakReferenceModuleItemDeclOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  weak_reference #(my_obj) wr;\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceModuleItemNonClassError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  weak_reference #(int) wr;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 2, "8.30.1"));
}

TEST(ClassConstraintElaboration, WeakReferenceForwardTypedefClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef class my_obj;\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_obj) weak_obj;\n"
             "  end\n"
             "endmodule\n"
             "class my_obj;\n"
             "  int x;\n"
             "endclass\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceTypedefAliasOfClassOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "typedef my_obj my_alias;\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_alias) wr;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceTypedefNonClassError) {
  ElabFixture f;
  ElabOk(
      "typedef enum {A, B} col_t;\n"
      "module m;\n"
      "  initial begin\n"
      "    weak_reference #(col_t) wr;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 4, "8.30.1"));
}

void ExpectNonClassWeakRefIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n  logic ok;\n  initial\n    " + stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "weak_reference needs a class type as its type parameter",
                    LineHolding(src, "weak_reference #(int) wr;"), "8.30.1"));
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassInAnAssertionPassStmt) {
  ExpectNonClassWeakRefIn("assert (ok) begin weak_reference #(int) wr; end");
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassInAnAssertionFailStmt) {
  ExpectNonClassWeakRefIn(
      "assert (ok) else begin weak_reference #(int) wr; end");
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassInARandcaseItem) {
  ExpectNonClassWeakRefIn(
      "randcase 1: begin weak_reference #(int) wr; end endcase");
}

TEST(ClassConstraintElaboration,
     WeakReferenceNonClassInARandsequenceCodeBlock) {
  ExpectNonClassWeakRefIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { begin weak_reference #(int) wr; end };\n"
      "      endsequence\n"
      "    end");
}

TEST(ClassConstraintElaboration,
     WeakReferenceNonClassInARandsequenceWeightCodeBlock) {
  ExpectNonClassWeakRefIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { begin weak_reference #(int) wr; end };\n"
      "        alt : { ok = 1; };\n"
      "      endsequence\n"
      "    end");
}

TEST(ClassConstraintElaboration, WeakReferenceStdScopedIsTheBuiltinClass) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  std::weak_reference#(my_obj) wref1;\n"
             "  initial begin\n"
             "    std::weak_reference#(my_obj) wref2;\n"
             "  end\n"
             "endmodule\n"));
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  std::weak_reference#(int) wref1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 2, "8.30.1"));
}

TEST(ClassConstraintElaboration, ModuleClassPropertyTypeArgumentIsChecked) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  class C;\n"
      "    weak_reference #(int) w;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 3, "8.30.1"));
}

}  // namespace
