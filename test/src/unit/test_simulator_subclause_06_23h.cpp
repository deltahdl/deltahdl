#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §6.23 with §8.11, §8.13 and §6.22.1: in a method, a type reference may name
// a property of the class bare or through `this`, a property the class
// inherits, or `this` itself, the class; a comparison of two such references
// holds exactly when the types match. A class declared in a module, in a
// package and in the compilation unit each answer alike.
struct ClassPlace {
  const char* name;
  // {0} is the classes, {1} the module's handle type.
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

// x and w are C's own properties, ib one C inherits from B; D is a class
// unrelated to C, and logic [0:7] differs from logic [7:0] by its bounds
// (§6.22.1(f)).
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

// The classes, with C's check() writing each of kCompared by `write`.
std::string Classes(std::string_view body) {
  return std::format(
      "  class D;\n  endclass\n"
      "  class B;\n    int ib;\n  endclass\n"
      "  class C extends B;\n    byte x;\n    logic [7:0] w;\n"
      "    function int check();\n      int r = 0;\n{}"
      "      return r;\n    endfunction\n  endclass\n",
      body);
}

// The bits kCompared gives, the first test's the most significant.
uint64_t Expected() {
  uint64_t bits = 0;
  for (const Compared& test : kCompared) bits = (bits << 1) | test.holds;
  return bits;
}

void ExpectInEveryPlace(const std::string& body) {
  const std::string kClasses = Classes(body);
  const std::string kHandle = "C";
  for (const ClassPlace& place : kClassPlaces) {
    SCOPED_TRACE(place.name);
    const std::string kSrc =
        std::vformat(place.text, std::make_format_args(kClasses, kHandle));
    SCOPED_TRACE(kSrc);
    EXPECT_EQ(RunAndGet(kSrc, "res"), Expected());
  }
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

}  // namespace
