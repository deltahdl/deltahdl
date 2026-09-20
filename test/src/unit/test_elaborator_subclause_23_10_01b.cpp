#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

// Parameter `name` of module `mod` once `src` is elaborated under top, or -1
// where the source does not elaborate, the module declares no such parameter
// or the fold left it unresolved: no case expects -1 of a parameter it reads.
int64_t ParamOfModule(const std::string& src, std::string_view mod,
                      std::string_view name, ElabFixture& f) {
  auto* design = ElaborateSrc(src, f, "top");
  if (design == nullptr) return -1;
  const auto* p = FindParam(design, mod, name);
  return p != nullptr && p->is_resolved ? p->resolved_value : -1;
}

// A module `name` declaring `parameter int TOP = 15`, a typedef `vec_t` of
// `logic [range]` and `parameter vec_t P = 0`, with B reading $bits(P).
std::string TypedefRangedModule(std::string_view name, std::string_view range) {
  std::string src = "module ";
  src += name;
  src +=
      ";\n"
      "  parameter int TOP = 15;\n"
      "  typedef logic [";
  src += range;
  src +=
      "] vec_t;\n"
      "  parameter vec_t P = 0;\n"
      "  localparam int B = $bits(P);\n"
      "endmodule\n";
  return src;
}

// §23.9 (printed page 761) makes a module a scope of its own and §6.18
// (printed 118) has a typedef name stand for the declaration of the scope it
// is written in, so two modules each declaring a `vec_t` of their own size
// their `parameter vec_t P` by their own typedef when a defparam makes TOP
// over: a's `logic [TOP:0]` under `defparam ua.TOP = 7` is 8 bits and b's
// `logic [TOP*4+3:0]` under `defparam ub.TOP = 3` is 16. Sized by the other
// module's typedef, a's P would read 32 bits and b's 4. The table the resize
// reads lays the module's own typedef items over the design-wide union
// (ModuleTypedefTable in src/elaborator/elaborator_defparam.cpp), which is
// what this pins.
TEST(DefparamElaboration, SizesEachModulesTypedefParameterByItsOwnTypedef) {
  const std::string kSrc = TypedefRangedModule("a", "TOP:0") +
                           TypedefRangedModule("b", "TOP*4+3:0") +
                           "module top;\n"
                           "  a ua();\n"
                           "  b ub();\n"
                           "  defparam ua.TOP = 7;\n"
                           "  defparam ub.TOP = 3;\n"
                           "endmodule\n";
  ElabFixture fa;
  EXPECT_EQ(ParamOfModule(kSrc, "a", "B", fa), 8);
  EXPECT_FALSE(fa.has_errors);
  ElabFixture fb;
  EXPECT_EQ(ParamOfModule(kSrc, "b", "B", fb), 16);
}

}  // namespace
