#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

// §35.6 "Calling imported functions": "The usage of imported functions is
// identical to the usage of native SystemVerilog functions. Hence the usage and
// syntax for calling imported functions is identical to the usage and syntax of
// native SystemVerilog functions. Specifically, arguments with default values
// can be omitted from the call; arguments can be bound by name if all formal
// arguments are named."
//
// The last clause of that sentence is a condition, and it is the one these
// cases are about. §35.5.4 makes a formal argument name optional in an import
// declaration -- "formal argument names are optional unless argument binding by
// name is needed" -- so an import can be declared with no names to bind to, and
// a call on one cannot use the named form. Nothing else in the tree brings the
// two rules together: the binding cases in
// test_simulator_subclause_35_06.cpp all declare named formals, and
// DpiImportCallArgs.AnUnknownNamedActualIsReported in
// test_elaborator_subclause_35_05.cpp misspells a name that does exist.
//
// "Identical to the usage of native SystemVerilog functions" is what decides
// the report: the rule reached is §13.5.4's, the same one a native call with an
// unmatched name breaks, so the report names that subclause rather than one of
// §35's.
namespace {

// §35.6: named binding needs formals with names, and this import has none, so
// there is nothing for `.a` to bind to and the call is reported.
TEST(DpiImportCallBinding, NamedBindingOnAnImportWithUnnamedFormalsIsReported) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int, input int);
      int r;
      initial r = sv_f(.a(1), .b(2));
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "no parameter 'a' in 'sv_f'",
                            5, "13.5.4"));
}

// The control, without which the case above would pass against an elaborator
// that rejected an unnamed formal outright rather than only the named binding
// on one. §35.5.4 permits the declaration, and §35.6 permits calling it; it is
// the named form alone that the missing names withdraw.
TEST(DpiImportCallBinding, PositionalBindingOnAnImportWithUnnamedFormalsIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int, input int);
      int r;
      initial r = sv_f(1, 2);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
