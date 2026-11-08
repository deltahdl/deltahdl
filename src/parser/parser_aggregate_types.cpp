#include <format>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_data_decl_internal.h"

namespace delta {

namespace {

void ApplyMemberType(StructMember& member, const DataType& member_type) {
  member.type_kind = member_type.kind;
  member.is_signed = member_type.is_signed;
  member.packed_dim_left = member_type.packed_dim_left;
  member.packed_dim_right = member_type.packed_dim_right;
  member.extra_packed_dims = member_type.extra_packed_dims;
  member.type_name = member_type.type_name;
  member.scope_name = member_type.scope_name;
  member.type_params = member_type.type_params;
}

bool IsStructOrUnionKw(TokenKind tk) {
  return tk == TokenKind::kKwStruct || tk == TokenKind::kKwUnion;
}

void CheckEnumBaseForm(const DataType& base, SourceLoc loc, DiagEngine& diag) {
  if (base.is_const) {
    diag.Error(loc, "an enumeration's base type takes no 'const'",
               Subclause("A.2.2.1"));
  }
  bool atom = ParserDataDeclHelpers::IsIntegerAtomKind(base.kind);
  bool vector_or_name = ParserDataDeclHelpers::IsIntegerVectorKind(base.kind) ||
                        base.kind == DataTypeKind::kNamed;
  bool none_written =
      base.kind == DataTypeKind::kImplicit && !base.signing_written;
  if (!atom && !vector_or_name && !none_written) {
    diag.Error(loc,
               "an enumeration's base type is an integer atom type, an "
               "integer vector type or a type name",
               Subclause("A.2.2.1"));
  } else if (atom && base.packed_dim_left != nullptr) {
    diag.Error(loc,
               "an integer atom type takes no packed dimension as an "
               "enumeration's base type",
               Subclause("A.2.2.1"));
  } else if (!base.extra_packed_dims.empty()) {
    diag.Error(loc,
               "an enumeration's base type takes at most one packed dimension",
               Subclause("A.2.2.1"));
  }
}

}  // namespace

DataType Parser::ParseEnumType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kEnum;
  dtype.decl_loc = CurrentLoc();
  Expect(TokenKind::kKwEnum, Subclause("6.19"));

  SourceLoc base_loc = CurrentLoc();
  auto base = ParseDataType();
  CheckEnumBaseForm(base, base_loc, diag_);
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

  DataType array;
  array.kind = DataTypeKind::kEnum;
  ParsePackedDims(array);
  if (array.packed_dim_left != nullptr) {
    dtype.enum_array_dims.emplace_back(array.packed_dim_left,
                                       array.packed_dim_right);
  }
  dtype.enum_array_dims.insert(dtype.enum_array_dims.end(),
                               array.extra_packed_dims.begin(),
                               array.extra_packed_dims.end());
  dtype.has_unsized_packed_dim = array.has_unsized_packed_dim;
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
  dtype.decl_loc = CurrentLoc();
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

DataType Parser::ParseStructMemberType() {
  DataType member_type;
  if (IsStructOrUnionKw(CurrentToken().kind)) {
    member_type = ParseStructOrUnionType();
    ParsePackedDims(member_type);
    return member_type;
  }
  if (Check(TokenKind::kKwEnum)) return ParseEnumType();
  if (ParserDataDeclHelpers::ReadTypeReference(*this, member_type)) {
    return member_type;
  }
  member_type = ParseDeclaredDataType();
  if (member_type.kind != DataTypeKind::kImplicit || !CheckIdentifier()) {
    return member_type;
  }
  auto saved = lexer_.SavePos();
  Token name_tok = Consume();
  if (!CheckIdentifier() && !Check(TokenKind::kLBracket)) {
    lexer_.RestorePos(saved);
    return member_type;
  }
  diag_.Error(name_tok.loc,
              std::format("declaration of type '{}' does not precede this "
                          "reference to it",
                          name_tok.text),
              Subclause("6.18"));
  member_type.kind = DataTypeKind::kNamed;
  member_type.type_name = name_tok.text;
  ParsePackedDims(member_type);
  return member_type;
}

void Parser::ParseStructMemberList(DataType& dtype, const DataType& member_type,
                                   const std::vector<Attribute>& member_attrs,
                                   bool is_rand, bool is_randc) {
  do {
    StructMember member;
    ApplyMemberType(member, member_type);
    if (member_type.kind == DataTypeKind::kStruct ||
        member_type.kind == DataTypeKind::kUnion ||
        member_type.kind == DataTypeKind::kEnum ||
        member_type.type_ref_expr != nullptr) {
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

  bool stalled = false;
  while (!Check(TokenKind::kRBrace) && !AtEnd() && !stalled) {
    auto member_attrs = ParseAttributes();
    bool is_rand = Match(TokenKind::kKwRand);
    bool is_randc = !is_rand && Match(TokenKind::kKwRandc);

    SourceLoc type_loc = CurrentLoc();
    DataType member_type = ParseStructMemberType();
    if (member_type.kind == DataTypeKind::kImplicit &&
        member_type.type_ref_expr == nullptr) {
      diag_.Error(type_loc,
                  "a structure or union member names a data type or void",
                  Subclause("A.2.2.1"));
      if (!CheckIdentifier()) {
        auto before = lexer_.SavePos().pos;
        Synchronize();
        stalled = lexer_.SavePos().pos == before;
        continue;
      }
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
