#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DpiDeclElab, DuplicateImportNameInSameModuleIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int foo(input int a);
      import "DPI-C" function int foo(input int a);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(DpiDeclElab, DistinctImportNamesInSameModuleOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int foo(input int a);
      import "DPI-C" function int bar(input int a);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiDeclElab, SameImportNameInDifferentModulesOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int foo(input int a);
    endmodule
    module n;
      import "DPI-C" function int foo(input int a);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiDeclElab, SignatureMismatchAcrossModulesByDefaultLinkageIsError) {
  // §35.5.4: when no c_identifier is given, the linkage name defaults to the
  // SystemVerilog name. Two declarations sharing that linkage must agree.
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int foo(input int a);
    endmodule
    module n;
      import "DPI-C" function int foo(input int a, input int b);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(DpiDeclElab, SignatureMismatchOnExplicitLinkageIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" my_link = function int sv_a(input int x);
    endmodule
    module n;
      import "DPI-C" my_link = function int sv_b(input bit x);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(DpiDeclElab, PureVsContextDifferenceUnderSameLinkageIsError) {
  // §35.5.4 includes the pure/context qualifiers in the type signature.
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = pure function int f(input int x);
    endmodule
    module n;
      import "DPI-C" link = context function int g(input int x);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(DpiDeclElab, MatchingSignatureUnderSameLinkageOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int x);
    endmodule
    module n;
      import "DPI-C" link = function int g(input int y);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiDeclElab, SignatureReturnTypeMismatchUnderSameLinkageIsError) {
  // The shared-linkage signature comparison includes the return type.
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int x);
    endmodule
    module n;
      import "DPI-C" link = function bit g(input int x);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(DpiDeclElab, SignatureSpecStringMismatchUnderSameLinkageIsError) {
  // The signature also includes the dpi_spec_string ("DPI-C" vs "DPI").
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function int f(input int x);
    endmodule
    module n;
      import "DPI" link = function int g(input int x);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(DpiDeclElab, SignatureArgDirectionMismatchUnderSameLinkageIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" link = function void f(input int x);
    endmodule
    module n;
      import "DPI-C" link = function void g(output int x);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
