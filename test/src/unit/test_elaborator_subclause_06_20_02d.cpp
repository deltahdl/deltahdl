#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_param_value_assignability.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ParamValueAssignability, NamedParameterIsFoundInEveryScope) {
  const IncompatibleValue kCases[] = {
      {"a package parameter named through its package",
       "package p;\n  parameter string S = \"s\";\nendpackage\nmodule m;\n"
       "  parameter int S = 1;\n  parameter int I = p::S;\nendmodule\n",
       "I", 6},
      {"a compilation-unit parameter named through $unit",
       "parameter string S = \"s\";\nmodule m;\n  parameter int S = 1;\n"
       "  parameter int I = $unit::S;\nendmodule\n",
       "I", 4},
      {"a class parameter named through its class",
       "class C;\n  parameter string S = \"s\";\nendclass\nmodule m;\n"
       "  parameter int S = 1;\n  parameter int I = C::S;\nendmodule\n",
       "I", 6},
      {"a parameter imported by name into a module",
       "package p;\n  parameter string S = \"s\";\nendpackage\nmodule m;\n"
       "  import p::S;\n  parameter int I = S;\nendmodule\n",
       "I", 6},
      {"a parameter imported by a wildcard into a module",
       "package p;\n  parameter string S = \"s\";\nendpackage\nmodule m;\n"
       "  import p::*;\n  parameter int I = S;\nendmodule\n",
       "I", 6},
      {"a parameter imported by the second of two wildcards",
       "package p;\n  parameter int T = 1;\nendpackage\npackage q;\n"
       "  parameter string S = \"s\";\nendpackage\nmodule m;\n"
       "  import p::*;\n  import q::*;\n  parameter int I = S;\nendmodule\n",
       "I", 10},
      {"a parameter imported into the compilation unit, named in a module",
       "package p;\n  parameter string S = \"s\";\nendpackage\nimport p::*;\n"
       "module m;\n  parameter int I = S;\nendmodule\n",
       "I", 6},
      {"a parameter imported into the compilation unit, named there",
       "package p;\n  parameter string S = \"s\";\nendpackage\nimport p::*;\n"
       "parameter int I = S;\nmodule m;\nendmodule\n",
       "I", 5},
      {"a parameter imported into another package",
       "package p;\n  parameter string S = \"s\";\nendpackage\npackage q;\n"
       "  import p::*;\n  parameter int I = S;\nendpackage\nmodule m;\n"
       "endmodule\n",
       "I", 6},
      {"a compilation-unit parameter named in a module",
       "parameter string S = \"s\";\nmodule m;\n  parameter int I = S;\n"
       "endmodule\n",
       "I", 3},
      {"a block parameter naming an earlier one of its block",
       "module m;\n  parameter int S = 1;\n  initial begin : b\n"
       "    parameter string S = \"s\";\n    parameter int I = S;\n  end\n"
       "endmodule\n",
       "I", 5},
      {"a block parameter naming one of an enclosing block",
       "module m;\n  initial begin : b\n    parameter string S = \"s\";\n"
       "    begin : c\n      parameter int I = S;\n    end\n  end\n"
       "endmodule\n",
       "I", 5},
      {"a block parameter naming a module parameter",
       "module m;\n  parameter string S = \"s\";\n  initial begin : b\n"
       "    parameter int I = S;\n  end\nendmodule\n",
       "I", 4},
      {"a block parameter naming a parameter of its generate block",
       "module m;\n  parameter int S = 1;\n  if (1) begin : g\n"
       "    parameter string S = \"s\";\n    initial begin : b\n"
       "      parameter int I = S;\n    end\n  end\nendmodule\n",
       "I", 6},
      {"a function parameter naming a parameter of its class",
       "class C;\n  parameter string S = \"s\";\n  function void f();\n"
       "    parameter int I = S;\n  endfunction\nendclass\nmodule m;\n"
       "endmodule\n",
       "I", 4},
      {"a function parameter naming a parameter of its package",
       "package p;\n  parameter string S = \"s\";\n"
       "  function automatic void f();\n    parameter int I = S;\n"
       "  endfunction\nendpackage\nmodule m;\nendmodule\n",
       "I", 4},
      {"a function parameter naming a compilation-unit parameter",
       "parameter string S = \"s\";\nfunction automatic void f();\n"
       "  parameter int I = S;\nendfunction\nmodule m;\nendmodule\n",
       "I", 3},
      {"an instance override in a generate block naming its parameter",
       "module c #(parameter int P = 1);\nendmodule\nmodule t;\n"
       "  parameter int W = 1;\n  if (1) begin : g\n"
       "    parameter string W = \"w\";\n    c #(.P(W)) u();\n  end\n"
       "endmodule\n",
       "P", 7},
      {"a defparam in a generate block naming its parameter",
       "module c;\n  parameter int P = 1;\nendmodule\nmodule t;\n"
       "  parameter int W = 1;\n  if (1) begin : g\n"
       "    parameter string W = \"w\";\n    c u();\n"
       "    defparam u.P = W;\n  end\nendmodule\n",
       "P", 9},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, NamedParameterOfItsTypeIsAcceptedInEveryScope) {
  const char* const kSources[] = {
      "package p;\n  parameter int S = 1;\nendpackage\n"
      "parameter int T = 1;\nclass C;\n  parameter int U = 1;\nendclass\n"
      "module m;\n  parameter string S = \"s\";\n"
      "  parameter string T = \"t\";\n  parameter string U = \"u\";\n"
      "  parameter int I = p::S;\n"
      "  parameter int J = $unit::T;\n  parameter int K = C::U;\nendmodule\n",
      "package p;\n  parameter int S = 1;\nendpackage\npackage q;\n"
      "  import p::*;\n  parameter T = S;\n  parameter U = p::S;\n"
      "endpackage\nmodule m;\n  parameter int I = q::T;\n"
      "  parameter int J = q::U;\nendmodule\n",
      "package p;\n  parameter string S = \"s\";\n  parameter int T = 1;\n"
      "endpackage\npackage q;\n  parameter int S = 1;\nendpackage\n"
      "module m;\n  import p::T;\n  import q::*;\n  parameter int I = S;\n"
      "endmodule\n",
      "package p;\n  parameter string S = \"s\";\nendpackage\n"
      "parameter string S = \"u\";\nmodule m;\n  import p::*;\n"
      "  parameter int S = 1;\n  parameter int I = S;\nendmodule\n",
      "module m;\n  parameter string S = \"s\";\n  initial begin : b\n"
      "    parameter int S = 1;\n    parameter int I = S;\n  end\n"
      "endmodule\n",
      "module m;\n  parameter int S = 1;\n  initial begin : b\n"
      "    begin : c\n      parameter string S = \"s\";\n    end\n"
      "    begin : d\n      parameter int I = S;\n    end\n  end\n"
      "endmodule\n",
      "class C;\n  parameter string S = \"s\";\n  function void f();\n"
      "    parameter int S = 1;\n    parameter int I = S;\n  endfunction\n"
      "endclass\nmodule m;\nendmodule\n",
      "module m;\n  parameter string S = \"s\";\n  if (1) begin : g\n"
      "    parameter int S = 1;\n    initial begin : b\n"
      "      parameter int I = S;\n    end\n  end\nendmodule\n",
      "module c #(parameter int P = 1);\nendmodule\nmodule t;\n"
      "  parameter string W = \"w\";\n  if (1) begin : g\n"
      "    parameter int W = 1;\n    c #(.P(W)) u();\n  end\nendmodule\n",
      "module c;\n  parameter int P = 1;\nendmodule\nmodule t;\n"
      "  parameter string W = \"w\";\n  if (1) begin : g\n"
      "    parameter int W = 1;\n    c u();\n    defparam u.P = W;\n"
      "  end\nendmodule\n",
  };
  ExpectEachAccepted(kSources);
}

TEST(ParamValueAssignability, SpecializationValueIsJudgedInEveryPlace) {
  const char* const kClass =
      "typedef enum {A, B} e_t;\nclass C #(e_t E = A);\nendclass\n";
  struct Place {
    const char* where;
    const char* rest;
    uint32_t line;
  };
  const Place kPlaces[] = {
      {"a module typedef", "module m;\n  typedef C #(1) c_t;\nendmodule\n", 5},
      {"a generate block variable",
       "module m;\n  if (1) begin : g\n    C #(1) h;\n  end\nendmodule\n", 6},
      {"a compilation-unit variable", "C #(1) h;\nmodule m;\nendmodule\n", 4},
      {"a compilation-unit typedef",
       "typedef C #(1) c_t;\nmodule m;\nendmodule\n", 4},
      {"a class property",
       "class D;\n  C #(1) h;\nendclass\nmodule m;\nendmodule\n", 5},
      {"a class typedef",
       "class D;\n  typedef C #(1) c_t;\nendclass\nmodule m;\nendmodule\n", 5},
      {"a procedure variable",
       "module m;\n  initial begin : b\n    C #(1) h;\n  end\nendmodule\n", 6},
      {"a function argument",
       "module m;\n  function void f(C #(1) h);\n  endfunction\nendmodule\n",
       5},
      {"a function return type",
       "module m;\n  function C #(1) f();\n    return null;\n"
       "  endfunction\nendmodule\n",
       5},
      {"a method variable",
       "class D;\n  function void f();\n    C #(1) h;\n  endfunction\n"
       "endclass\nmodule m;\nendmodule\n",
       6},
      {"a compilation-unit function argument",
       "function automatic void f(C #(1) h);\nendfunction\nmodule m;\n"
       "endmodule\n",
       4},
  };
  for (const Place& place : kPlaces) {
    SCOPED_TRACE(place.where);
    const std::string kSrc = std::string(kClass) + place.rest;
    std::string allowed = kSrc;
    allowed.replace(allowed.find("#(1)"), 4, "#(B)");
    ElabFixture reported;
    ElaborateSrc(kSrc, reported);
    EXPECT_TRUE(ReportedError(reported.diag.Diagnostics(), NotAssignable("E"),
                              place.line, "6.20.2"));
    ElabFixture accepted;
    ElaborateSrc(allowed, accepted);
    EXPECT_FALSE(accepted.has_errors);
  }
}

TEST(ParamValueAssignability, SpecializationArgumentOfAnotherTypeIsReported) {
  const IncompatibleValue kCases[] = {
      {"a package variable",
       "package p;\n  typedef enum {A, B} e_t;\n  class C #(e_t E = A);\n"
       "  endclass\n  C #(1) h;\nendpackage\nmodule m;\nendmodule\n",
       "E", 5},
      {"a package typedef",
       "package p;\n  typedef enum {A, B} e_t;\n  class C #(e_t E = A);\n"
       "  endclass\n  typedef C #(1) c_t;\nendpackage\nmodule m;\n"
       "endmodule\n",
       "E", 5},
      {"a module parameter",
       "class C #(string S = \"a\");\nendclass\nmodule m;\n"
       "  parameter int W = 1;\n  C #(.S(W)) h;\nendmodule\n",
       "S", 5},
      {"a generate block parameter",
       "class C #(string S = \"a\");\nendclass\nmodule m;\n"
       "  parameter string W = \"w\";\n  if (1) begin : g\n"
       "    parameter int W = 1;\n    C #(.S(W)) h;\n  end\nendmodule\n",
       "S", 7},
      {"a class parameter",
       "class C #(string S = \"a\");\nendclass\nclass D;\n"
       "  parameter int W = 1;\n  C #(.S(W)) h;\nendclass\nmodule m;\n"
       "endmodule\n",
       "S", 5},
      {"a block parameter",
       "class C #(string S = \"a\");\nendclass\nmodule m;\n"
       "  initial begin : b\n    parameter int W = 1;\n"
       "    C #(.S(W)) h;\n  end\nendmodule\n",
       "S", 6},
      {"an imported parameter",
       "package p;\n  parameter int W = 1;\nendpackage\n"
       "class C #(string S = \"a\");\nendclass\nmodule m;\n  import p::*;\n"
       "  C #(.S(W)) h;\nendmodule\n",
       "S", 8},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, SpecializationArgumentOfItsTypeIsAccepted) {
  const char* const kSources[] = {
      "package p;\n  typedef enum {A, B} e_t;\n  class C #(e_t E = A);\n"
      "  endclass\n  C #(B) h;\n  typedef C #(B) c_t;\nendpackage\n"
      "module m;\nendmodule\n",
      "class C #(string S = \"a\");\nendclass\nclass D;\n"
      "  parameter string W = \"w\";\n  C #(.S(W)) h;\nendclass\nmodule m;\n"
      "  parameter int W = 1;\n  if (1) begin : g\n"
      "    parameter string W = \"g\";\n    C #(.S(W)) h;\n  end\n"
      "  initial begin : b\n    parameter string W = \"b\";\n"
      "    C #(.S(W)) h;\n  end\nendmodule\n",
      "interface i #(parameter int N = 1);\nendinterface\nmodule m;\n"
      "  virtual i #(.N(2)) v;\nendmodule\n",
  };
  ExpectEachAccepted(kSources);
}

TEST(ParamValueAssignability, UntypedParameterTakesTheTypeOfTheValueItNames) {
  const IncompatibleValue kCases[] = {
      {"a module parameter",
       "module m;\n  parameter string S = \"s\";\n  parameter T = S;\n"
       "  parameter int I = T;\nendmodule\n",
       "I", 4},
      {"a generate block parameter",
       "module m;\n  parameter int S = 1;\n  if (1) begin : g\n"
       "    parameter string S = \"s\";\n    parameter T = S;\n"
       "    parameter int I = T;\n  end\nendmodule\n",
       "I", 6},
      {"a compilation-unit parameter",
       "parameter string S = \"s\";\nparameter T = S;\n"
       "parameter int I = T;\nmodule m;\nendmodule\n",
       "I", 3},
      {"a package parameter named through its package",
       "package p;\n  parameter string S = \"s\";\n  parameter T = S;\n"
       "endpackage\nmodule m;\n  parameter int I = p::T;\nendmodule\n",
       "I", 6},
      {"a class parameter",
       "class C;\n  parameter string S = \"s\";\n  parameter T = S;\n"
       "  parameter int I = T;\nendclass\nmodule m;\nendmodule\n",
       "I", 4},
      {"a block parameter",
       "module m;\n  initial begin : b\n    parameter string S = \"s\";\n"
       "    parameter T = S;\n    parameter int I = T;\n  end\n"
       "endmodule\n",
       "I", 5},
      {"a module parameter naming an imported one",
       "package p;\n  parameter string S = \"s\";\nendpackage\nmodule m;\n"
       "  import p::*;\n  parameter T = S;\n  parameter int I = T;\n"
       "endmodule\n",
       "I", 7},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, UntypedParameterValueIsNamedFromItsOwnScope) {
  const char* const kSources[] = {
      "module m;\n  parameter int S = 1;\n  parameter T = S;\n"
      "  initial begin : b\n    parameter string S = \"s\";\n"
      "    parameter int I = T;\n  end\nendmodule\n",
      "package p;\n  parameter int S = 1;\n  parameter T = S;\nendpackage\n"
      "module m;\n  parameter string S = \"s\";\n"
      "  parameter int I = p::T;\nendmodule\n",
      "class C;\n  parameter int S = 1;\n  parameter T = S;\nendclass\n"
      "module m;\n  parameter string S = \"s\";\n"
      "  parameter int I = C::T;\nendmodule\n",
      "typedef enum {A, B} e_t;\nmodule c;\n  parameter X = 0;\n"
      "  parameter Y = X;\n  parameter e_t E = Y;\nendmodule\nmodule t;\n"
      "  c u();\n  defparam u.X = B;\nendmodule\n",
  };
  ExpectEachAccepted(kSources);
}

}  // namespace
