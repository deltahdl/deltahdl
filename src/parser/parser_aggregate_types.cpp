// The enumeration, structure and union types of IEEE 1800-2023 §6.19 and
// §7.2, read where a data type stands: the enum body of §6.19 and the member
// list of §7.2, with the packed, signing and tagged qualifiers §7.2.1, §7.2.2
// and §7.3.2 let stand before it. Moved here from parser_declaration.cpp,
// which the A.1.9 report on a `default` argument took past the limit
// assert-no-oversized-source-files enforces; the forward typedefs that name
// these kinds stay with the typedef in that file.

#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "parser/parser.h"

namespace delta {

namespace {

// §7.2.1: a struct/union member declarator inherits the shared member type's
// kind, sign, packed dimensions, type name and, for a name written behind a
// package or class qualifier (§26.3, §8.23), the qualifier, `q` of `q::pair_t
// Add`; dropping the qualifier left the member to be looked up by the bare
// name, which a wildcard import might make stand for another declaration.
// Pure field copy.
void ApplyMemberType(StructMember& member, const DataType& member_type) {
  member.type_kind = member_type.kind;
  member.is_signed = member_type.is_signed;
  member.packed_dim_left = member_type.packed_dim_left;
  member.packed_dim_right = member_type.packed_dim_right;
  member.extra_packed_dims = member_type.extra_packed_dims;
  member.type_name = member_type.type_name;
  member.scope_name = member_type.scope_name;
}

// §7.2: a struct or union keyword introduces an aggregate member type.
bool IsStructOrUnionKw(TokenKind tk) {
  return tk == TokenKind::kKwStruct || tk == TokenKind::kKwUnion;
}

}  // namespace

DataType Parser::ParseEnumType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kEnum;
  Expect(TokenKind::kKwEnum, Subclause("6.19"));

  auto base = ParseDataType();
  if (base.kind != DataTypeKind::kImplicit) {
    dtype.is_signed = base.is_signed;
    dtype.packed_dim_left = base.packed_dim_left;
    dtype.packed_dim_right = base.packed_dim_right;

    dtype.enum_base_kind = base.kind;

    if (base.kind == DataTypeKind::kNamed) {
      dtype.enum_base_name = base.type_name;
    }
  }

  dtype = ParseEnumBody(dtype);

  return dtype;
}

DataType Parser::ParseEnumBody(const DataType& base) {
  DataType dtype = base;
  Expect(TokenKind::kLBrace, Subclause("6.19"));
  do {
    EnumMember member;
    member.name = Expect(TokenKind::kIdentifier, Subclause("6.19")).text;

    if (Match(TokenKind::kLBracket)) {
      member.range_start = ParseEnumRangeBound();
      if (Match(TokenKind::kColon)) {
        member.range_end = ParseEnumRangeBound();
      }
      Expect(TokenKind::kRBracket, Subclause("6.19.2"));
    }
    if (Match(TokenKind::kEq)) {
      member.value = ParseExpr();
    }
    dtype.enum_members.push_back(member);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kRBrace, Subclause("6.19"));
  return dtype;
}

// §6.19.2 (Syntax 6-5, A.2.2.1): an enum_name_declaration writes its range
// as `[ integral_number [ : integral_number ] ]`, and Table 6-10 has each
// bound be a positive or non-negative integral number, so a bound is a number
// as A.8.7 spells one -- `3`, `'d3`, `4'h3` -- and never a constant
// expression: `VAL[N]` over a parameter N names no constant, however N folds,
// and `VAL[(3)]` is no integral_number either. The bound is read as an
// expression, for the recovery that gives, and one that is not a number token
// alone is reported where it starts; the member keeps it, so a walk over the
// declaration sees the range it was written with.
Expr* Parser::ParseEnumRangeBound() {
  Expr* bound = ParseExpr();
  if (bound != nullptr &&
      (bound->kind != ExprKind::kIntegerLiteral || bound->is_parenthesized)) {
    diag_.Error(bound->range.start,
                "enumeration range bound must be an integral number",
                Subclause("6.19.2"));
  }
  return bound;
}

// §7.3.2: a union may carry at most one of the 'soft'/'tagged' qualifiers; a
// stray second one is diagnosed and discarded.
void Parser::ParseUnionQualifiers(DataType& dtype) {
  auto reject_dup_union_qualifier = [&](TokenKind other) {
    if (!Check(other)) return;
    diag_.Error(CurrentLoc(),
                "union may have at most one of 'soft' or 'tagged'",
                Subclause("7.2"));
    Consume();
  };
  if (Match(TokenKind::kKwTagged)) {
    dtype.is_tagged = true;
    reject_dup_union_qualifier(TokenKind::kKwSoft);
  } else if (Match(TokenKind::kKwSoft)) {
    dtype.is_soft = true;
    reject_dup_union_qualifier(TokenKind::kKwTagged);
  }
}

// §7.2.1 (Syntax 7-1): 'signing' may appear only after 'packed'. An unpacked
// structure or union cannot carry a signedness specifier, so a stray
// signed/unsigned is rejected and dropped to recover cleanly before the member
// list.
void Parser::ParseStructPackedSigning(DataType& dtype) {
  if (Match(TokenKind::kKwPacked)) {
    dtype.is_packed = true;
    if (Match(TokenKind::kKwSigned)) {
      dtype.is_signed = true;
    } else {
      Match(TokenKind::kKwUnsigned);
    }
    return;
  }
  if (Check(TokenKind::kKwSigned) || Check(TokenKind::kKwUnsigned)) {
    diag_.Error(CurrentLoc(),
                "signing is not allowed on an unpacked structure or union",
                Subclause("7.2"));
    Consume();
  }
}

DataType Parser::ParseStructOrUnionType() {
  DataType dtype;
  dtype.kind = Check(TokenKind::kKwStruct) ? DataTypeKind::kStruct
                                           : DataTypeKind::kUnion;
  Consume();

  if (dtype.kind == DataTypeKind::kUnion) ParseUnionQualifiers(dtype);
  ParseStructPackedSigning(dtype);

  if (CheckIdentifier() && !Check(TokenKind::kLBrace)) {
    diag_.Error(CurrentLoc(),
                dtype.kind == DataTypeKind::kStruct
                    ? "structure declarations may not have a tag before '{'"
                    : "union declarations may not have a tag before '{'",
                Subclause("7.2"));
    Consume();
  }

  ParseStructMembers(dtype);
  return dtype;
}

DataType Parser::ParseStructOrUnionBody(TokenKind kw) {
  DataType dtype;
  dtype.kind = (kw == TokenKind::kKwStruct) ? DataTypeKind::kStruct
                                            : DataTypeKind::kUnion;
  ParseStructMembers(dtype);
  return dtype;
}

// Parse the data_type that prefixes a struct/union member declaration,
// including any nested struct/union/enum with its packed dimensions. A.2.2.1
// lets the type be a type_identifier behind a package_scope or a class_scope,
// `q::pair_t Add` (§26.3, §8.23), which ParseDeclaredDataType reads past
// known_types_, where a package name never stands; ParseDataType left `q` to
// be read as the member's name and the `::` after it as a missing semicolon.
DataType Parser::ParseStructMemberType() {
  DataType member_type;
  if (IsStructOrUnionKw(CurrentToken().kind)) {
    member_type = ParseStructOrUnionType();
    ParsePackedDims(member_type);
    return member_type;
  }
  if (Check(TokenKind::kKwEnum)) {
    member_type = ParseEnumType();
    ParsePackedDims(member_type);
    return member_type;
  }
  member_type = ParseDeclaredDataType();
  return member_type;
}

// Parse the comma-separated list of declarators sharing one member type and
// append them to dtype.
void Parser::ParseStructMemberList(DataType& dtype, const DataType& member_type,
                                   const std::vector<Attribute>& member_attrs,
                                   bool is_rand, bool is_randc) {
  do {
    StructMember member;
    ApplyMemberType(member, member_type);
    // §7.2.1: retain the full type for inline aggregate/enum members so a
    // nested member's bit width can be recovered during width evaluation
    // (ApplyMemberType keeps only the member's own kind and packed dims).
    if (member_type.kind == DataTypeKind::kStruct ||
        member_type.kind == DataTypeKind::kUnion ||
        member_type.kind == DataTypeKind::kEnum) {
      member.nested_type = arena_.Create<DataType>(member_type);
    }
    member.is_rand = is_rand;
    member.is_randc = is_randc;
    member.attrs = member_attrs;
    member.name = Expect(TokenKind::kIdentifier, Subclause("7.2")).text;
    ParseUnpackedDims(member.unpacked_dims);
    if (Match(TokenKind::kEq)) {
      member.init_expr = ParseExpr();
    }
    dtype.struct_members.push_back(member);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("7.2"));
}

void Parser::ParseStructMembers(DataType& dtype) {
  auto open_brace_loc = CurrentLoc();
  Expect(TokenKind::kLBrace, Subclause("7.2"));

  while (!Check(TokenKind::kRBrace) && !AtEnd()) {
    auto member_attrs = ParseAttributes();
    bool is_rand = Match(TokenKind::kKwRand);
    bool is_randc = !is_rand && Match(TokenKind::kKwRandc);

    DataType member_type = ParseStructMemberType();
    if (member_type.kind == DataTypeKind::kImplicit && !CheckIdentifier()) {
      Synchronize();
      continue;
    }
    ParseStructMemberList(dtype, member_type, member_attrs, is_rand, is_randc);
  }
  if (dtype.struct_members.empty()) {
    diag_.Error(open_brace_loc,
                dtype.kind == DataTypeKind::kStruct
                    ? "struct body must contain at least one member"
                    : "union body must contain at least one member",
                Subclause("7.2"));
  }
  Expect(TokenKind::kRBrace, Subclause("7.2"));
}

}  // namespace delta
