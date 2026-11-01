#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

// One generate-block item, with the declarations it reads and the text written
// ahead of the module that declares them.
struct GenerateBlockItem {
  // Written on the first line, before `module m;`: a class or an interface the
  // declarations name.
  std::string head;
  // The declarations `item` reads.
  std::string decls;
  // The item written inside the generate block.
  std::string item;
};

// The line every source InsideGenerateBlocks builds writes the item on.
inline constexpr uint32_t kGenerateBlockItemLine = 4;

// `module m` holding `form.item` on its fourth line inside a generate block,
// once for each place the block can stand: a conditional generate block, a
// block nested in a loop generate block, the default block of a case generate
// construct, and a conditional generate block that declares `form.decls`
// itself rather than reading the module's. §27.2 makes every one of them a
// collection of module items, so a rule that holds of a module item holds of
// the item in each.
inline std::vector<std::string> InsideGenerateBlocks(
    const GenerateBlockItem& form) {
  const std::string kModule = form.head + "module m;\n";
  const std::string kTop = kModule + "  " + form.decls + "\n";
  return {
      kTop + "  if (1) begin : g\n    " + form.item + "\n  end\nendmodule\n",
      kTop +
          "  for (genvar i = 0; i < 2; i++) begin : g\n    if (1) begin : h " +
          form.item + " end\n  end\nendmodule\n",
      kTop + "  case (1)\n    0: begin : skipped end default: begin : g " +
          form.item + " end\n  endcase\nendmodule\n",
      kModule + "  if (1) begin : g\n    " + form.decls + "\n    " + form.item +
          "\n  end\nendmodule\n",
  };
}

// Whether every source InsideGenerateBlocks builds of `form` is rejected with
// `message` under `subclause` on the item's line.
inline ::testing::AssertionResult RejectedInsideGenerateBlocks(
    const GenerateBlockItem& form, std::string_view message,
    std::string_view subclause) {
  for (const std::string& src : InsideGenerateBlocks(form)) {
    ElabFixture f;
    ElaborateSrc(src, f);
    auto reported = ReportedError(f.diag.Diagnostics(), message,
                                  kGenerateBlockItemLine, subclause);
    if (!reported) return reported << "\nin\n" << src;
  }
  return ::testing::AssertionSuccess();
}

// Whether every source InsideGenerateBlocks builds of `form` elaborates
// without an error.
inline ::testing::AssertionResult AcceptedInsideGenerateBlocks(
    const GenerateBlockItem& form) {
  for (const std::string& src : InsideGenerateBlocks(form)) {
    if (!ElabOk(src)) {
      return ::testing::AssertionFailure() << "rejected\n" << src;
    }
  }
  return ::testing::AssertionSuccess();
}
