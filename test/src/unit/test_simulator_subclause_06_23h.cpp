#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

struct ClassPlace {
  const char* name;
  const char* text;
};

constexpr std::array kClassPlaces = {
    ClassPlace{"class declared in a module",
               "module t;\n{0}  int res;\n  initial begin\n    {1} h;\n"
               "    h = new;\n    res = h.check();\n  end\nendmodule\n"},
    ClassPlace{"class declared in a package",
               "package p;\n{0}endpackage\nmodule t;\n  int res;\n"
               "  initial begin\n    p::{1} h;\n    h = new;\n"
               "    res = h.check();\n  end\nendmodule\n"},
    ClassPlace{"class declared in the compilation unit",
               "{0}module t;\n  int res;\n  initial begin\n    {1} h;\n"
               "    h = new;\n    res = h.check();\n  end\nendmodule\n"},
};

struct Compared {
  const char* text;
  bool holds;
};

constexpr std::array kCompared = {
    Compared{"type(x) == type(byte)", true},
    Compared{"type(x) != type(byte)", false},
    Compared{"type(this.x) == type(byte)", true},
    Compared{"type(this.x) == type(int)", false},
    Compared{"type(ib) == type(int)", true},
    Compared{"type(this.ib) != type(int)", false},
    Compared{"type(w) == type(logic [7:0])", true},
    Compared{"type(w) == type(logic [0:7])", false},
    Compared{"type(this) == type(C)", true},
    Compared{"type(this) == type(D)", false},
    Compared{"type(this) != type(B)", true},
};

std::string Classes(std::string_view body) {
  return std::format(
      "  class D;\n  endclass\n"
      "  class B;\n    int ib;\n  endclass\n"
      "  class C extends B;\n    byte x;\n    logic [7:0] w;\n"
      "    function int check();\n      int r = 0;\n{}"
      "      return r;\n    endfunction\n  endclass\n",
      body);
}

uint64_t Expected() {
  uint64_t bits = 0;
  for (const Compared& test : kCompared) bits = (bits << 1) | test.holds;
  return bits;
}

void ExpectEveryPlaceGives(const std::string& classes, std::string_view handle,
                           uint64_t expected) {
  for (const ClassPlace& place : kClassPlaces) {
    SCOPED_TRACE(place.name);
    const std::string kSrc =
        std::vformat(place.text, std::make_format_args(classes, handle));
    SCOPED_TRACE(kSrc);
    EXPECT_EQ(RunAndGet(kSrc, "res"), expected);
  }
}

void ExpectInEveryPlace(const std::string& body) {
  ExpectEveryPlaceGives(Classes(body), "C", Expected());
}

TEST(ClassMethodTypeRefSim, ComparisonInAProceduralIf) {
  std::string body;
  const size_t kLast = kCompared.size() - 1;
  for (size_t k = 0; k < kCompared.size(); ++k) {
    body += std::format("      if ({}) r[{}] = 1'b1;\n", kCompared[k].text,
                        kLast - k);
  }
  ExpectInEveryPlace(body);
}

TEST(ClassMethodTypeRefSim, ComparisonInAnAssignment) {
  std::string body = "      r = {";
  for (size_t k = 0; k < kCompared.size(); ++k) {
    if (k > 0) body += ", ";
    body += std::format("1'({})", kCompared[k].text);
  }
  body += "};\n";
  ExpectInEveryPlace(body);
}

TEST(ClassMethodTypeRefSim, PackageValuesInAnotherScopesClass) {
  constexpr std::array kHosts = {
      "package q;\n  import p::*;\n{}endpackage\nmodule t;\n  int res;\n"
      "  initial begin\n    q::c h;\n    h = new;\n    res = h.check();\n"
      "  end\nendmodule\n",
      "import p::*;\n{}module t;\n  int res;\n  initial begin\n    c h;\n"
      "    h = new;\n    res = h.check();\n  end\nendmodule\n",
  };
  const std::string kPackage =
      "package p;\n  byte v;\n  parameter byte P = 3;\n"
      "  typedef enum byte {E0, E1} e_t;\nendpackage\n";
  const std::string kClass =
      "  class c;\n    function int check();\n      int r = 0;\n"
      "      var type(p::v + 1'b0) d;\n"
      "      if (type(p::v + 1'b0) == type(logic [7:0])) r[7] = 1'b1;\n"
      "      if (type(p::v) == type(logic [7:0])) r[6] = 1'b1;\n"
      "      if (type(v[3:0]) == type(bit [3:0])) r[5] = 1'b1;\n"
      "      if (type(P) == type(byte)) r[4] = 1'b1;\n"
      "      if (type(E1) == type(p::e_t)) r[3] = 1'b1;\n"
      "      if (type(p::E1 + 1'b0) == type(logic [7:0])) r[2] = 1'b1;\n"
      "      r[1] = $bits(d) == 8 && $isunknown(d);\n"
      "      r[0] = type(d) == type(byte);\n"
      "      return r;\n    endfunction\n  endclass\n";
  for (const char* host : kHosts) {
    const std::string kSrc =
        kPackage + std::vformat(host, std::make_format_args(kClass));
    SCOPED_TRACE(kSrc);
    EXPECT_EQ(RunAndGet(kSrc, "res"), 0b1011'1110u);
  }
}

struct Specialization {
  const char* handle;
  uint64_t expected;
};

constexpr std::array kSpecializations = {
    Specialization{"K", 0b1010'1010},
    Specialization{"K #()", 0b1010'1010},
    Specialization{"K #(int, 8)", 0b1010'1010},
    Specialization{"K #(int, 4)", 0b1010'1001},
    Specialization{"K #(byte, 8)", 0b0101'0110},
    Specialization{"K #(byte, 4)", 0b0101'0101},
};

TEST(ClassMethodTypeRefSim, ParameterizedClassJudgesEachSpecialization) {
  const std::string kClass =
      "  typedef int word_t;\n"
      "  class K #(type U = int, int N = 8);\n"
      "    U y;\n    logic [N-1:0] z;\n"
      "    function int check();\n      int r = 0;\n"
      "      if (type(U) == type(word_t)) r[7] = 1'b1;\n"
      "      if (type(word_t) != type(U)) r[6] = 1'b1;\n"
      "      if (type(U) == type(int)) r[5] = 1'b1;\n"
      "      if (type(U) != type(int)) r[4] = 1'b1;\n"
      "      if (type(y) == type(int)) r[3] = 1'b1;\n"
      "      if (type(y) != type(int)) r[2] = 1'b1;\n"
      "      if (type(z) == type(logic [7:0])) r[1] = 1'b1;\n"
      "      if (type(z) != type(logic [7:0])) r[0] = 1'b1;\n"
      "      return r;\n    endfunction\n  endclass\n";
  for (const Specialization& spec : kSpecializations) {
    SCOPED_TRACE(spec.handle);
    ExpectEveryPlaceGives(kClass, spec.handle, spec.expected);
  }
}

TEST(ClassMethodTypeRefSim, ClassOfAnInstanceJudgesItsOwnTypeParameter) {
  constexpr std::array kHosts = {"module", "interface", "program"};
  for (const char* host : kHosts) {
    const std::string kSrc = std::format(
        "{0} sub #(type T = int);\n"
        "  class c;\n    function int check();\n      int r = 0;\n"
        "      if (type(T) == type(int)) r[1] = 1'b1;\n"
        "      if (type(T) != type(int)) r[0] = 1'b1;\n"
        "      return r;\n    endfunction\n  endclass\n"
        "  int res;\n"
        "  initial begin\n    c h;\n    h = new;\n    res = h.check();\n"
        "  end\nend{0}\n"
        "module top;\n  sub u0();\n  sub #(.T(byte)) u1();\n"
        "  sub #(.T(int)) u2();\nendmodule\n",
        host);
    SCOPED_TRACE(kSrc);
    EXPECT_EQ(RunAndGet(kSrc, "u0.res"), 0b10u);
    EXPECT_EQ(RunAndGet(kSrc, "u1.res"), 0b01u);
    EXPECT_EQ(RunAndGet(kSrc, "u2.res"), 0b10u);
  }
}

}  // namespace
