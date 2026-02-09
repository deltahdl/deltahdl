#include <gtest/gtest.h>

#include <string_view>

#include "synthesis/liberty.h"

using namespace delta;

// =============================================================================
// Parse empty library
// =============================================================================

TEST(Liberty, ParseEmptyLibrary) {
  constexpr std::string_view kSrc = R"lib(
    library(testlib) {
    }
  )lib";
  auto lib = ParseLiberty(kSrc);
  EXPECT_EQ(lib.library_name, "testlib");
  EXPECT_TRUE(lib.cells.empty());
}

// =============================================================================
// Parse library with one cell, one pin
// =============================================================================

TEST(Liberty, ParseOneCellOnePin) {
  constexpr std::string_view kSrc = R"lib(
    library(mylib) {
      cell(BUF) {
        pin(A) {
          direction : input;
        }
        pin(Y) {
          direction : output;
          function : "A";
        }
      }
    }
  )lib";
  auto lib = ParseLiberty(kSrc);
  EXPECT_EQ(lib.library_name, "mylib");
  ASSERT_EQ(lib.cells.size(), 1);

  const auto& cell = lib.cells[0];
  EXPECT_EQ(cell.name, "BUF");
  ASSERT_EQ(cell.pins.size(), 2);

  EXPECT_EQ(cell.pins[0].name, "A");
  EXPECT_EQ(cell.pins[0].direction, "input");

  EXPECT_EQ(cell.pins[1].name, "Y");
  EXPECT_EQ(cell.pins[1].direction, "output");
  EXPECT_EQ(cell.pins[1].function, "A");
}

// =============================================================================
// Parse library with timing data
// =============================================================================

TEST(Liberty, ParseTimingData) {
  constexpr std::string_view kSrc = R"lib(
    library(timlib) {
      cell(AND2) {
        pin(A) { direction : input; }
        pin(B) { direction : input; }
        pin(Y) { direction : output; function : "A * B"; }
        timing() {
          related_pin : "A";
          cell_rise : 0.05;
          cell_fall : 0.03;
        }
      }
    }
  )lib";
  auto lib = ParseLiberty(kSrc);
  ASSERT_EQ(lib.cells.size(), 1);
  ASSERT_EQ(lib.cells[0].timing.size(), 1);

  const auto& t = lib.cells[0].timing[0];
  EXPECT_EQ(t.related_pin, "A");
  EXPECT_FLOAT_EQ(t.cell_rise, 0.05f);
  EXPECT_FLOAT_EQ(t.cell_fall, 0.03f);
}

// =============================================================================
// Parse multiple cells
// =============================================================================

TEST(Liberty, ParseMultipleCells) {
  constexpr std::string_view kSrc = R"lib(
    library(multilib) {
      cell(INV) {
        area : 1.0;
        pin(A) { direction : input; }
        pin(Y) { direction : output; function : "!A"; }
      }
      cell(AND2) {
        area : 2.0;
        pin(A) { direction : input; }
        pin(B) { direction : input; }
        pin(Y) { direction : output; function : "A * B"; }
      }
    }
  )lib";
  auto lib = ParseLiberty(kSrc);
  ASSERT_EQ(lib.cells.size(), 2);
  EXPECT_EQ(lib.cells[0].name, "INV");
  EXPECT_EQ(lib.cells[1].name, "AND2");
}

// =============================================================================
// Parse pin function expressions
// =============================================================================

TEST(Liberty, ParsePinFunctionExpressions) {
  constexpr std::string_view kSrc = R"lib(
    library(funclib) {
      cell(OR2) {
        pin(A) { direction : input; }
        pin(B) { direction : input; }
        pin(Y) { direction : output; function : "A + B"; }
      }
      cell(NAND2) {
        pin(A) { direction : input; }
        pin(B) { direction : input; }
        pin(Y) { direction : output; function : "!(A * B)"; }
      }
    }
  )lib";
  auto lib = ParseLiberty(kSrc);
  ASSERT_EQ(lib.cells.size(), 2);
  EXPECT_EQ(lib.cells[0].pins[2].function, "A + B");
  EXPECT_EQ(lib.cells[1].pins[2].function, "!(A * B)");
}

// =============================================================================
// Parse cell area values
// =============================================================================

TEST(Liberty, ParseCellAreaValues) {
  constexpr std::string_view kSrc = R"lib(
    library(arealib) {
      cell(INV) {
        area : 1.5;
        pin(A) { direction : input; }
        pin(Y) { direction : output; function : "!A"; }
      }
      cell(AND4) {
        area : 4.0;
        pin(A) { direction : input; }
        pin(B) { direction : input; }
        pin(C) { direction : input; }
        pin(D) { direction : input; }
        pin(Y) { direction : output; function : "A * B * C * D"; }
      }
    }
  )lib";
  auto lib = ParseLiberty(kSrc);
  ASSERT_EQ(lib.cells.size(), 2);
  EXPECT_FLOAT_EQ(lib.cells[0].area, 1.5f);
  EXPECT_FLOAT_EQ(lib.cells[1].area, 4.0f);
}
