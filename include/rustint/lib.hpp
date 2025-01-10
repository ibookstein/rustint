#pragma once

#include <climits>
#include <concepts>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <limits>
#include <optional>
#include <string_view>
#include <tuple>

#define rustint_unimplemented()                                                \
  do {                                                                         \
    std::fprintf(stderr, "UNIMPLEMENTED at %s:%s:%s", __FILE__, __LINE__,      \
                 __func__);                                                    \
    std::abort();                                                              \
  } while (false)

namespace rustint {

using i8 = std::int8_t;
using u8 = std::uint8_t;
using i16 = std::int16_t;
using u16 = std::uint16_t;
using i32 = std::int32_t;
using u32 = std::uint32_t;
using i64 = std::int64_t;
using u64 = std::uint64_t;
using i128 = __int128;
using u128 = unsigned __int128;
using isize = std::make_signed_t<std::size_t>;
using usize = std::size_t;

template <typename T> T abs(T x) { return std::abs(x); }

template <typename T> T abs_diff(T x, T y) { return x > y ? x - y : y - x; }

template <typename T>
std::optional<T> checked_abs(T x)
  requires std::signed_integral<T>
{
  return x == std::numeric_limits<T>::min() ? std::nullopt
                                            : std::make_optional(std::abs(x));
}

template <typename T> std::tuple<T, bool> borrowing_sub(T x, T y, bool borrow) {
  rustint_unimplemented();
}

template <typename T> std::tuple<T, bool> carrying_add(T x, T y, bool carry) {
  rustint_unimplemented();
}

template <typename T> std::tuple<T, T> carrying_mul(T x, T y) {
  rustint_unimplemented();
}

template <typename T> std::optional<T> checked_add(T x, T y) {
  rustint_unimplemented();
}

// -----------------------------------------------------------------------------
// RInt class
// Each method trivially delegates to the corresponding free function(s).
// -----------------------------------------------------------------------------
template <std::integral T> class RInt {
private:
  using UT = std::make_unsigned_t<T>;
  using ST = std::make_signed_t<T>;
  using TBYTES = std::array<u8, sizeof(T)>;

public:
  T val;

  constexpr RInt(T v) : val(v) {}
  constexpr T operator()() const { return val; }

  static constexpr RInt from(T v) { return RInt(v); }
  static constexpr RInt MAX() { return RInt(std::numeric_limits<T>::max()); }
  static constexpr RInt MIN() { return RInt(std::numeric_limits<T>::min()); }
  static constexpr u32 BITS() { return static_cast<u32>(CHAR_BIT * sizeof(T)); }

  static constexpr RInt max_value() { return MAX(); }
  static constexpr RInt min_value() { return MIN(); }

  // ---------------------------------------------------------------------------
  // borrowing_sub, carrying_add, carrying_mul
  // ---------------------------------------------------------------------------
  constexpr auto borrowing_sub(this RInt self, RInt rhs, bool bin) {
    auto [res, bout] = rustint::borrowing_sub(self.val, rhs.val, bin);
    return std::make_tuple(RInt(res), bout);
  }

  constexpr auto carrying_add(this RInt self, RInt rhs, bool cin) {
    auto [res, cout] = rustint::carrying_add(self.val, rhs.val, cin);
    return std::make_tuple(RInt(res), cout);
  }

  constexpr auto carrying_mul(this RInt self, RInt rhs)
    requires std::unsigned_integral<T>
  {
    auto [lo, hi] = rustint::carrying_mul(self.val, rhs.val);
    return std::make_tuple(RInt(lo), RInt(hi));
  }

  // ---------------------------------------------------------------------------
  // abs, abs_diff
  // ---------------------------------------------------------------------------
  constexpr auto abs(this RInt self)
    requires std::signed_integral<T>
  {
    return RInt(rustint::abs(self.val));
  }

  constexpr auto abs_diff(this RInt self, RInt rhs) {
    return RInt(rustint::abs_diff(self.val, rhs.val));
  }

  // ---------------------------------------------------------------------------
  // cast_signed, cast_unsigned
  // ---------------------------------------------------------------------------
  constexpr auto cast_signed(this RInt self)
    requires std::unsigned_integral<T>
  {
    return RInt<ST>(static_cast<ST>(self.val));
  }

  constexpr auto cast_unsigned(this RInt self)
    requires std::signed_integral<T>
  {
    return RInt<UT>(static_cast<UT>(self.val));
  }

  // ---------------------------------------------------------------------------
  // checked_* methods
  // ---------------------------------------------------------------------------
  constexpr auto checked_abs(this RInt self)
    requires std::signed_integral<T>
  {
    return rustint::checked_abs(self.val).transform(from);
  }

  constexpr auto checked_add(this RInt self, RInt rhs) {
    return rustint::checked_add(self.val, rhs.val).transform(from);
  }

  constexpr auto checked_add_signed(this RInt self, RInt<ST> rhs)
    requires std::unsigned_integral<T>
  {
    return rustint::checked_add_signed(self.val, rhs.val).transform(from);
  }

  constexpr auto checked_add_unsigned(this RInt self, RInt<UT> rhs)
    requires std::signed_integral<T>
  {
    return rustint::checked_add_unsigned(self.val, rhs.val).transform(from);
  }

  constexpr auto checked_div(this RInt self, RInt rhs) {
    return rustint::checked_div(self.val, rhs.val).transform(from);
  }

  constexpr auto checked_div_euclid(this RInt self, RInt rhs) {
    return rustint::checked_div_euclid(self.val, rhs.val).transform(from);
  }

  constexpr auto checked_ilog(this RInt self, RInt base) {
    return rustint::checked_ilog(self.val, base.val).transform(from);
  }

  constexpr auto checked_ilog2(this RInt self) {
    return rustint::checked_ilog2(self.val).transform(from);
  }

  constexpr auto checked_ilog10(this RInt self) {
    return rustint::checked_ilog10(self.val).transform(from);
  }

  constexpr auto checked_isqrt(this RInt self)
    requires std::signed_integral<T>
  {
    return rustint::checked_isqrt(self.val).transform(from);
  }

  constexpr auto checked_mul(this RInt self, RInt rhs) {
    return rustint::checked_mul(self.val, rhs.val).transform(from);
  }

  constexpr auto checked_neg(this RInt self)
    requires std::signed_integral<T>
  {
    return rustint::checked_neg(self.val).transform(from);
  }

  constexpr auto checked_next_multiple_of(this RInt self, RInt rhs) {
    return rustint::checked_next_multiple_of(self.val, rhs.val).transform(from);
  }

  constexpr auto checked_next_power_of_two(this RInt self)
    requires std::unsigned_integral<T>
  {
    return rustint::checked_next_power_of_two(self.val).transform(from);
  }

  constexpr auto checked_pow(this RInt self, u32 exp) {
    return rustint::checked_pow(self.val, exp).transform(from);
  }

  constexpr auto checked_rem(this RInt self, RInt rhs) {
    return rustint::checked_rem(self.val, rhs.val).transform(from);
  }

  constexpr auto checked_rem_euclid(this RInt self, RInt rhs) {
    return rustint::checked_rem_euclid(self.val, rhs.val).transform(from);
  }

  constexpr auto checked_shl(this RInt self, u32 shift) {
    return rustint::checked_shl(self.val, shift).transform(from);
  }

  constexpr auto checked_shr(this RInt self, u32 shift) {
    return rustint::checked_shr(self.val, shift).transform(from);
  }

  constexpr auto checked_signed_diff(this RInt self, RInt rhs)
    requires std::unsigned_integral<T>
  {
    return rustint::checked_signed_diff(self.val, rhs.val).transform(from);
  }

  constexpr auto checked_sub(this RInt self, RInt rhs) {
    return rustint::checked_sub(self.val, rhs.val).transform(from);
  }

  constexpr auto checked_sub_unsigned(this RInt self, RInt<UT> rhs)
    requires std::signed_integral<T>
  {
    return rustint::checked_sub_unsigned(self.val, rhs.val).transform(from);
  }

  // ---------------------------------------------------------------------------
  // count_ones, count_zeros
  // ---------------------------------------------------------------------------
  constexpr auto count_ones(this RInt self) {
    return RInt(rustint::count_ones(self.val));
  }

  constexpr auto count_zeros(this RInt self) {
    return RInt(rustint::count_zeros(self.val));
  }

  // ---------------------------------------------------------------------------
  // div_ceil, div_euclid, div_floor
  // ---------------------------------------------------------------------------
  constexpr auto div_ceil(this RInt self, RInt rhs) {
    return RInt(rustint::div_ceil(self.val, rhs.val));
  }

  constexpr auto div_euclid(this RInt self, RInt rhs) {
    return RInt(rustint::div_euclid(self.val, rhs.val));
  }

  constexpr auto div_floor(this RInt self, RInt rhs) {
    return RInt(rustint::div_floor(self.val, rhs.val));
  }

  // ---------------------------------------------------------------------------
  // Bytes & Endianness
  // ---------------------------------------------------------------------------
  static constexpr RInt from_be(RInt x) {
    return RInt(rustint::from_be(x.val));
  }

  static constexpr RInt from_le(RInt x) {
    return RInt(rustint::from_le(x.val));
  }

  static constexpr RInt from_ne(RInt x) {
    return RInt(rustint::from_ne(x.val));
  }

  static constexpr RInt from_be_bytes(TBYTES bytes) {
    return RInt(rustint::from_be_bytes(bytes));
  }

  static constexpr RInt from_le_bytes(TBYTES bytes) {
    return RInt(rustint::from_le_bytes(bytes));
  }

  static constexpr RInt from_ne_bytes(TBYTES bytes) {
    return RInt(rustint::from_ne_bytes(bytes));
  }

  constexpr auto to_be(this RInt self) {
    return RInt(rustint::to_be(self.val));
  }

  constexpr auto to_be_bytes(this RInt self) {
    return rustint::to_be_bytes(self.val);
  }

  constexpr auto to_le(this RInt self) {
    return RInt(rustint::to_le(self.val));
  }

  constexpr auto to_le_bytes(this RInt self) {
    return rustint::to_le_bytes(self.val);
  }

  constexpr auto to_ne_bytes(this RInt self) {
    return rustint::to_ne_bytes(self.val);
  }

  // ---------------------------------------------------------------------------
  // midpoint
  // ---------------------------------------------------------------------------
  constexpr auto midpoint(this RInt self, RInt rhs) {
    return RInt(rustint::midpoint(self.val, rhs.val));
  }

  // ---------------------------------------------------------------------------
  // from_str_radix
  // ---------------------------------------------------------------------------
  static constexpr std::optional<RInt> from_str_radix(std::string_view s,
                                                      u32 base) {
    return rustint::from_str_radix<T>(s, base).transform(from);
  }

  // ---------------------------------------------------------------------------
  // ilog, ilog2, ilog10, isqrt
  // ---------------------------------------------------------------------------
  constexpr auto ilog(this RInt self, RInt base) {
    return RInt(rustint::ilog(self.val, base.val));
  }

  constexpr auto ilog2(this RInt self) {
    return RInt(rustint::ilog2(self.val));
  }

  constexpr auto ilog10(this RInt self) {
    return RInt(rustint::ilog10(self.val));
  }

  constexpr auto isqrt(this RInt self)
    requires std::signed_integral<T>
  {
    return RInt(rustint::isqrt(self.val));
  }

  // ---------------------------------------------------------------------------
  // is_multiple_of, is_negative, is_positive, is_power_of_two
  // ---------------------------------------------------------------------------
  constexpr auto is_multiple_of(this RInt self, RInt rhs)
    requires std::unsigned_integral<T>
  {
    return rustint::is_multiple_of(self.val, rhs.val);
  }

  constexpr auto is_negative(this RInt self)
    requires std::signed_integral<T>
  {
    return rustint::is_negative(self.val);
  }

  constexpr auto is_positive(this RInt self)
    requires std::signed_integral<T>
  {
    return rustint::is_positive(self.val);
  }

  constexpr auto is_power_of_two(this RInt self)
    requires std::unsigned_integral<T>
  {
    return rustint::is_power_of_two(self.val);
  }

  // ---------------------------------------------------------------------------
  // leading/trailing ones/zeros
  // ---------------------------------------------------------------------------
  constexpr auto leading_ones(this RInt self) {
    return RInt(rustint::leading_ones(self.val));
  }

  constexpr auto leading_zeros(this RInt self) {
    return RInt(rustint::leading_zeros(self.val));
  }

  constexpr auto trailing_ones(this RInt self) {
    return RInt(rustint::trailing_ones(self.val));
  }

  constexpr auto trailing_zeros(this RInt self) {
    return RInt(rustint::trailing_zeros(self.val));
  }

  // ---------------------------------------------------------------------------
  // next_multiple_of, next_power_of_two
  // ---------------------------------------------------------------------------
  constexpr auto next_multiple_of(this RInt self, RInt rhs) {
    return RInt(rustint::next_multiple_of(self.val, rhs.val));
  }

  constexpr auto next_power_of_two(this RInt self)
    requires std::unsigned_integral<T>
  {
    return RInt(rustint::next_power_of_two(self.val));
  }

  // ---------------------------------------------------------------------------
  // overflowing_*
  // ---------------------------------------------------------------------------
  constexpr auto overflowing_abs(this RInt self)
    requires std::signed_integral<T>
  {
    auto [res, of] = rustint::overflowing_abs(self.val);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_add(this RInt self, RInt rhs) {
    auto [res, of] = rustint::overflowing_add(self.val, rhs.val);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_add_signed(this RInt self, RInt<ST> rhs)
    requires std::unsigned_integral<T>
  {
    auto [res, of] = rustint::overflowing_add_signed(self.val, rhs.val);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_add_unsigned(this RInt self, RInt<UT> rhs)
    requires std::signed_integral<T>
  {
    auto [res, of] = rustint::overflowing_add_unsigned(self.val, rhs.val);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_div(this RInt self, RInt rhs) {
    auto [res, of] = rustint::overflowing_div(self.val, rhs.val);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_div_euclid(this RInt self, RInt rhs) {
    auto [res, of] = rustint::overflowing_div_euclid(self.val, rhs.val);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_mul(this RInt self, RInt rhs) {
    auto [res, of] = rustint::overflowing_mul(self.val, rhs.val);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_neg(this RInt self)
    requires std::signed_integral<T>
  {
    auto [res, of] = rustint::overflowing_neg(self.val);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_pow(this RInt self, u32 exp) {
    auto [res, of] = rustint::overflowing_pow(self.val, exp);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_rem(this RInt self, RInt rhs) {
    auto [res, of] = rustint::overflowing_rem(self.val, rhs.val);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_rem_euclid(this RInt self, RInt rhs) {
    auto [res, of] = rustint::overflowing_rem_euclid(self.val, rhs.val);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_shl(this RInt self, u32 shift) {
    auto [res, of] = rustint::overflowing_shl(self.val, shift);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_shr(this RInt self, u32 shift) {
    auto [res, of] = rustint::overflowing_shr(self.val, shift);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_sub(this RInt self, RInt rhs) {
    auto [res, of] = rustint::overflowing_sub(self.val, rhs.val);
    return std::make_pair(RInt(res), of);
  }

  constexpr auto overflowing_sub_unsigned(this RInt self, RInt<UT> rhs)
    requires std::signed_integral<T>
  {
    auto [res, of] = rustint::overflowing_sub_unsigned(self.val, rhs.val);
    return std::make_pair(RInt(res), of);
  }

  // ---------------------------------------------------------------------------
  // pow, rem_euclid, reverse_bits, rotate_left, rotate_right
  // ---------------------------------------------------------------------------
  constexpr auto pow(this RInt self, u32 exp) {
    return RInt(rustint::pow(self.val, exp));
  }

  constexpr auto rem_euclid(this RInt self, RInt rhs) {
    return RInt(rustint::rem_euclid(self.val, rhs.val));
  }

  constexpr auto reverse_bits(this RInt self) {
    return RInt(rustint::reverse_bits(self.val));
  }

  constexpr auto rotate_left(this RInt self, u32 n) {
    return RInt(rustint::rotate_left(self.val, n));
  }

  constexpr auto rotate_right(this RInt self, u32 n) {
    return RInt(rustint::rotate_right(self.val, n));
  }

  // ---------------------------------------------------------------------------
  // saturating_*
  // ---------------------------------------------------------------------------
  constexpr auto saturating_abs(this RInt self)
    requires std::signed_integral<T>
  {
    return RInt(rustint::saturating_abs(self.val));
  }

  constexpr auto saturating_add(this RInt self, RInt rhs) {
    return RInt(rustint::saturating_add(self.val, rhs.val));
  }

  constexpr auto saturating_add_signed(this RInt self, RInt<ST> rhs)
    requires std::unsigned_integral<T>
  {
    return RInt(rustint::saturating_add_signed(self.val, rhs.val));
  }

  constexpr auto saturating_add_unsigned(this RInt self, RInt<UT> rhs)
    requires std::signed_integral<T>
  {
    return RInt(rustint::saturating_add_unsigned(self.val, rhs.val));
  }

  constexpr auto saturating_div(this RInt self, RInt rhs) {
    return RInt(rustint::saturating_div(self.val, rhs.val));
  }

  constexpr auto saturating_mul(this RInt self, RInt rhs) {
    return RInt(rustint::saturating_mul(self.val, rhs.val));
  }

  constexpr auto saturating_neg(this RInt self)
    requires std::signed_integral<T>
  {
    return RInt(rustint::saturating_neg(self.val));
  }

  constexpr auto saturating_pow(this RInt self, u32 exp) {
    return RInt(rustint::saturating_pow(self.val, exp));
  }

  constexpr auto saturating_sub(this RInt self, RInt rhs) {
    return RInt(rustint::saturating_sub(self.val, rhs.val));
  }

  constexpr auto saturating_sub_unsigned(this RInt self, RInt<UT> rhs)
    requires std::signed_integral<T>
  {
    return RInt(rustint::saturating_sub_unsigned(self.val, rhs.val));
  }

  // ---------------------------------------------------------------------------
  // signum
  // ---------------------------------------------------------------------------
  constexpr auto signum(this RInt self)
    requires std::signed_integral<T>
  {
    return RInt(rustint::signum(self.val));
  }

  // ---------------------------------------------------------------------------
  // strict_*
  // ---------------------------------------------------------------------------
  constexpr auto strict_abs(this RInt self)
    requires std::signed_integral<T>
  {
    return RInt(rustint::strict_abs(self.val));
  }

  constexpr auto strict_add(this RInt self, RInt rhs) {
    return RInt(rustint::strict_add(self.val, rhs.val));
  }

  constexpr auto strict_add_signed(this RInt self, RInt<ST> rhs)
    requires std::unsigned_integral<T>
  {
    return RInt(rustint::strict_add_signed(self.val, rhs.val));
  }

  constexpr auto strict_add_unsigned(this RInt self, RInt<UT> rhs)
    requires std::signed_integral<T>
  {
    return RInt(rustint::strict_add_unsigned(self.val, rhs.val));
  }

  constexpr auto strict_div(this RInt self, RInt rhs) {
    return RInt(rustint::strict_div(self.val, rhs.val));
  }

  constexpr auto strict_div_euclid(this RInt self, RInt rhs) {
    return RInt(rustint::strict_div_euclid(self.val, rhs.val));
  }

  constexpr auto strict_mul(this RInt self, RInt rhs) {
    return RInt(rustint::strict_mul(self.val, rhs.val));
  }

  constexpr auto strict_neg(this RInt self)
    requires std::signed_integral<T>
  {
    return RInt(rustint::strict_neg(self.val));
  }

  constexpr auto strict_pow(this RInt self, u32 exp) {
    return RInt(rustint::strict_pow(self.val, exp));
  }

  constexpr auto strict_rem(this RInt self, RInt rhs) {
    return RInt(rustint::strict_rem(self.val, rhs.val));
  }

  constexpr auto strict_rem_euclid(this RInt self, RInt rhs) {
    return RInt(rustint::strict_rem_euclid(self.val, rhs.val));
  }

  constexpr auto strict_shl(this RInt self, u32 shift) {
    return RInt(rustint::strict_shl(self.val, shift));
  }

  constexpr auto strict_shr(this RInt self, u32 shift) {
    return RInt(rustint::strict_shr(self.val, shift));
  }

  constexpr auto strict_sub(this RInt self, RInt rhs) {
    return RInt(rustint::strict_sub(self.val, rhs.val));
  }

  constexpr auto strict_sub_unsigned(this RInt self, RInt<UT> rhs)
    requires std::signed_integral<T>
  {
    return RInt(rustint::strict_sub_unsigned(self.val, rhs.val));
  }

  // ---------------------------------------------------------------------------
  // swap_bytes
  // ---------------------------------------------------------------------------
  constexpr auto swap_bytes(this RInt self) {
    return RInt(rustint::swap_bytes(self.val));
  }

  // ---------------------------------------------------------------------------
  // unbounded_shl, unbounded_shr
  // ---------------------------------------------------------------------------
  constexpr auto unbounded_shl(this RInt self, u64 shift) {
    return RInt(rustint::unbounded_shl(self.val, shift));
  }

  constexpr auto unbounded_shr(this RInt self, u64 shift) {
    return RInt(rustint::unbounded_shr(self.val, shift));
  }

  // ---------------------------------------------------------------------------
  // unchecked_*
  // ---------------------------------------------------------------------------
  constexpr auto unchecked_add(this RInt self, RInt rhs) {
    return RInt(rustint::unchecked_add(self.val, rhs.val));
  }

  constexpr auto unchecked_mul(this RInt self, RInt rhs) {
    return RInt(rustint::unchecked_mul(self.val, rhs.val));
  }

  constexpr auto unchecked_neg(this RInt self)
    requires std::signed_integral<T>
  {
    return RInt(rustint::unchecked_neg(self.val));
  }

  constexpr auto unchecked_shl(this RInt self, u32 shift) {
    return RInt(rustint::unchecked_shl(self.val, shift));
  }

  constexpr auto unchecked_shr(this RInt self, u32 shift) {
    return RInt(rustint::unchecked_shr(self.val, shift));
  }

  constexpr auto unchecked_sub(this RInt self, RInt rhs) {
    return RInt(rustint::unchecked_sub(self.val, rhs.val));
  }

  // ---------------------------------------------------------------------------
  // unsigned_abs => reinterpret negative bits
  // ---------------------------------------------------------------------------
  constexpr auto unsigned_abs(this RInt self)
    requires std::signed_integral<T>
  {
    return RInt<UT>(rustint::unsigned_abs(self.val));
  }

  // ---------------------------------------------------------------------------
  // widening_mul => for T unsigned => returns (low, high)
  // ---------------------------------------------------------------------------
  constexpr auto widening_mul(this RInt self, RInt rhs)
    requires std::unsigned_integral<T>
  {
    auto [lo, hi] = rustint::widening_mul(self.val, rhs.val);
    return std::make_pair(RInt(lo), RInt(hi));
  }

  // ---------------------------------------------------------------------------
  // wrapping_*
  // ---------------------------------------------------------------------------
  constexpr auto wrapping_abs(this RInt self)
    requires std::signed_integral<T>
  {
    return RInt(rustint::wrapping_abs(self.val));
  }

  constexpr auto wrapping_add(this RInt self, RInt rhs) {
    return RInt(rustint::wrapping_add(self.val, rhs.val));
  }

  constexpr auto wrapping_add_signed(this RInt self, RInt<ST> rhs)
    requires std::unsigned_integral<T>
  {
    return RInt(rustint::wrapping_add_signed<T, ST>(self.val, rhs.val));
  }

  constexpr auto wrapping_add_unsigned(this RInt self, RInt<UT> rhs)
    requires std::signed_integral<T>
  {
    return RInt(rustint::wrapping_add_unsigned<T, UT>(self.val, rhs.val));
  }

  constexpr auto wrapping_div(this RInt self, RInt rhs) {
    return RInt(rustint::wrapping_div(self.val, rhs.val));
  }

  constexpr auto wrapping_div_euclid(this RInt self, RInt rhs) {
    return RInt(rustint::wrapping_div_euclid(self.val, rhs.val));
  }

  constexpr auto wrapping_mul(this RInt self, RInt rhs) {
    return RInt(rustint::wrapping_mul(self.val, rhs.val));
  }

  constexpr auto wrapping_neg(this RInt self) {
    return RInt(rustint::wrapping_neg(self.val));
  }

  constexpr auto wrapping_next_power_of_two(this RInt self)
    requires std::unsigned_integral<T>
  {
    return RInt(rustint::wrapping_next_power_of_two(self.val));
  }

  constexpr auto wrapping_pow(this RInt self, u32 exp) {
    return RInt(rustint::wrapping_pow(self.val, exp));
  }

  constexpr auto wrapping_rem(this RInt self, RInt rhs) {
    return RInt(rustint::wrapping_rem(self.val, rhs.val));
  }

  constexpr auto wrapping_rem_euclid(this RInt self, RInt rhs) {
    return RInt(rustint::wrapping_rem_euclid(self.val, rhs.val));
  }

  constexpr auto wrapping_shl(this RInt self, RInt rhs) {
    return RInt(rustint::wrapping_shl(self.val, rhs.val));
  }

  constexpr auto wrapping_shr(this RInt self, RInt rhs) {
    return RInt(rustint::wrapping_shr(self.val, rhs.val));
  }

  constexpr auto wrapping_sub(this RInt self, RInt rhs) {
    return RInt(rustint::wrapping_sub(self.val, rhs.val));
  }

  constexpr auto wrapping_sub_unsigned(this RInt self, RInt<UT> rhs)
    requires std::signed_integral<T>
  {
    return RInt(rustint::wrapping_sub_unsigned(self.val, rhs.val));
  }
};

} // namespace rustint
