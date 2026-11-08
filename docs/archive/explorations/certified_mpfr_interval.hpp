#ifndef CERTIFIED_MPFR_INTERVAL_HPP
#define CERTIFIED_MPFR_INTERVAL_HPP

// Directed interval arithmetic and second-order jets, with no native
// floating-point arithmetic in proof bounds. See INTERVAL_ARITHMETIC_ENGINE.md.
// All storage uses the documented MPFR Custom Interface, not private fields.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <limits>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <mpfr.h>

#ifndef CERTIFIED_MPFR_BITS
#define CERTIFIED_MPFR_BITS 80
#endif

namespace certified {

constexpr mpfr_prec_t precision = CERTIFIED_MPFR_BITS;
static_assert(precision >= 64, "all 64-bit integral constants must be exact");
static_assert(GMP_NAIL_BITS == 0, "this engine requires GMP without nails");

class R {
    static constexpr std::size_t limbs = (precision + GMP_NUMB_BITS - 1) / GMP_NUMB_BITS;
    std::array<mp_limb_t, limbs> significand_{};
    mpfr_t value_;
public:
    R() noexcept {
        mpfr_custom_init(significand_.data(), precision);
        mpfr_custom_init_set(value_, MPFR_ZERO_KIND, 0, precision, significand_.data());
    }
    template<class T, std::enable_if_t<std::is_integral_v<T>, int> = 0>
    R(T n) : R() {
        static_assert(sizeof(T) <= sizeof(std::uintmax_t), "integer too large");
        if constexpr (std::is_signed_v<T>)
            mpfr_set_sj(value_, static_cast<std::intmax_t>(n), MPFR_RNDN);
        else mpfr_set_uj(value_, static_cast<std::uintmax_t>(n), MPFR_RNDN);
    }
    R(const R& other) noexcept : R() { mpfr_set(value_, other.value_, MPFR_RNDN); }
    R(R&& other) noexcept : R(other) {}
    R& operator=(const R& other) noexcept {
        if (this != &other) mpfr_set(value_, other.value_, MPFR_RNDN);
        return *this;
    }
    R& operator=(R&& other) noexcept { return *this = other; }
    // No mpfr_clear: Custom Interface storage belongs to this object.
    mpfr_ptr ptr() noexcept { return value_; }
    mpfr_srcptr ptr() const noexcept { return value_; }
    int sign() const noexcept { return mpfr_sgn(value_); }
    bool zero() const noexcept { return mpfr_zero_p(value_); }
    bool finite() const noexcept { return mpfr_number_p(value_); }
    double get_d(mpfr_rnd_t rnd = MPFR_RNDN) const noexcept {
        return mpfr_get_d(value_, rnd); // Diagnostics or search heuristics only.
    }
    static R binary64(double x) {
        if (!std::isfinite(x)) throw std::domain_error("nonfinite binary64 input");
        R out;
        if (mpfr_set_d(out.ptr(), x, MPFR_RNDN) != 0)
            throw std::runtime_error("binary64 input was not represented exactly");
        return out;
    }
    static R parse(const char* text, mpfr_rnd_t rnd, int base = 10) {
        R out;
        if (mpfr_set_str(out.ptr(), text, base, rnd) != 0 || !out.finite())
            throw std::domain_error("invalid or nonfinite MPFR input");
        return out;
    }
    std::string str() const {
        char text[160];
        mpfr_snprintf(text, sizeof(text), "%.30Rg", value_);
        return text; // Human-readable, not a serialization of an exact bound.
    }
    friend bool operator<(const R& a, const R& b) noexcept { return mpfr_less_p(a.ptr(), b.ptr()); }
    friend bool operator>(const R& a, const R& b) noexcept { return b < a; }
    friend bool operator<=(const R& a, const R& b) noexcept { return mpfr_lessequal_p(a.ptr(), b.ptr()); }
    friend bool operator>=(const R& a, const R& b) noexcept { return b <= a; }
    friend bool operator==(const R& a, const R& b) noexcept { return mpfr_equal_p(a.ptr(), b.ptr()); }
    friend bool operator!=(const R& a, const R& b) noexcept { return !(a == b); }
    friend R operator-(const R& a) {
        R out;
        mpfr_neg(out.ptr(), a.ptr(), MPFR_RNDN); // Exact sign change.
        return out;
    }
};

inline void require_finite(const R& x) {
    if (!x.finite()) throw std::range_error("nonfinite MPFR arithmetic result");
}

// Explicit rounding is mandatory for point arithmetic. In particular there
// is deliberately no R operator+ followed by an ineffective rd/ru wrapper.
inline R add(const R& a, const R& b, mpfr_rnd_t rnd) {
    R out; mpfr_add(out.ptr(), a.ptr(), b.ptr(), rnd); require_finite(out); return out;
}
inline R sub(const R& a, const R& b, mpfr_rnd_t rnd) {
    R out; mpfr_sub(out.ptr(), a.ptr(), b.ptr(), rnd); require_finite(out); return out;
}
inline R mul(const R& a, const R& b, mpfr_rnd_t rnd) {
    R out; mpfr_mul(out.ptr(), a.ptr(), b.ptr(), rnd); require_finite(out); return out;
}
inline R div(const R& a, const R& b, mpfr_rnd_t rnd) {
    if (b.zero()) throw std::domain_error("zero point denominator");
    R out; mpfr_div(out.ptr(), a.ptr(), b.ptr(), rnd); require_finite(out); return out;
}
inline R square(const R& a, mpfr_rnd_t rnd) {
    R out; mpfr_sqr(out.ptr(), a.ptr(), rnd); require_finite(out); return out;
}
inline R root(const R& a, mpfr_rnd_t rnd) {
    if (a.sign() < 0) throw std::domain_error("negative square root");
    R out; mpfr_sqrt(out.ptr(), a.ptr(), rnd); require_finite(out); return out;
}
inline R logarithm(const R& a, mpfr_rnd_t rnd) {
    if (a.sign() <= 0) throw std::domain_error("nonpositive logarithm");
    R out; mpfr_log(out.ptr(), a.ptr(), rnd); require_finite(out); return out;
}
inline R arctangent(const R& a, mpfr_rnd_t rnd) {
    R out; mpfr_atan(out.ptr(), a.ptr(), rnd); require_finite(out); return out;
}
inline R exponential(const R& a, mpfr_rnd_t rnd) {
    R out; mpfr_exp(out.ptr(), a.ptr(), rnd); require_finite(out); return out;
}
inline R rmin(const R& a, const R& b) { return a < b ? a : b; }
inline R rmax(const R& a, const R& b) { return a > b ? a : b; }
inline R abs(const R& a) { return a.sign() < 0 ? -a : a; }

struct I {
    R l, h;
    I() = default;
    template<class T, std::enable_if_t<std::is_integral_v<T>, int> = 0>
    I(T n) : l(n), h(n) {}
    I(const R& a) : l(a), h(a) { require_finite(l); }
    I(const R& a, const R& b) : l(a), h(b) { require_finite(l); require_finite(h); }
    static I rational(std::intmax_t numerator, std::uintmax_t denominator = 1) {
        if (denominator == 0) throw std::domain_error("zero rational denominator");
        R n(numerator), d(denominator);
        return {div(n, d, MPFR_RNDD), div(n, d, MPFR_RNDU)};
    }
    static I from_q(mpq_srcptr q) {
        I out;
        mpfr_set_q(out.l.ptr(), q, MPFR_RNDD);
        mpfr_set_q(out.h.ptr(), q, MPFR_RNDU);
        require_finite(out.l); require_finite(out.h);
        return out;
    }
    static I decimal(const char* text) {
        return {R::parse(text, MPFR_RNDD), R::parse(text, MPFR_RNDU)};
    }
    static I binary64(double x) { return I(R::binary64(x)); }
    bool empty() const noexcept { return l > h; }
    bool zero() const noexcept { return l.zero() && h.zero(); }
    bool contains_zero() const noexcept { return l.sign() <= 0 && h.sign() >= 0; }
    void valid() const {
        if (empty()) throw std::domain_error("arithmetic on an empty interval");
        require_finite(l); require_finite(h);
    }
};

inline I operator+(const I& a, const I& b) {
    a.valid(); b.valid();
    if (a.zero()) return b;
    if (b.zero()) return a;
    return {add(a.l, b.l, MPFR_RNDD), add(a.h, b.h, MPFR_RNDU)};
}
inline I operator-(const I& a, const I& b) {
    a.valid(); b.valid();
    if (b.zero()) return a;
    return {sub(a.l, b.h, MPFR_RNDD), sub(a.h, b.l, MPFR_RNDU)};
}
inline I operator-(const I& a) { a.valid(); return {-a.h, -a.l}; }
inline I operator*(const I& a, const I& b) {
    a.valid(); b.valid();
    if (a.zero() || b.zero()) return I(0);
    // The sign partition selects exact extrema before directed evaluation.
    if (a.l.sign() >= 0) {
        if (b.l.sign() >= 0)
            return {mul(a.l,b.l,MPFR_RNDD),mul(a.h,b.h,MPFR_RNDU)};
        if (b.h.sign() <= 0)
            return {mul(a.h,b.l,MPFR_RNDD),mul(a.l,b.h,MPFR_RNDU)};
        return {mul(a.h,b.l,MPFR_RNDD),mul(a.h,b.h,MPFR_RNDU)};
    }
    if (a.h.sign() <= 0) {
        if (b.l.sign() >= 0)
            return {mul(a.l,b.h,MPFR_RNDD),mul(a.h,b.l,MPFR_RNDU)};
        if (b.h.sign() <= 0)
            return {mul(a.h,b.h,MPFR_RNDD),mul(a.l,b.l,MPFR_RNDU)};
        return {mul(a.l,b.h,MPFR_RNDD),mul(a.l,b.l,MPFR_RNDU)};
    }
    if (b.l.sign() >= 0)
        return {mul(a.l,b.h,MPFR_RNDD),mul(a.h,b.h,MPFR_RNDU)};
    if (b.h.sign() <= 0)
        return {mul(a.h,b.l,MPFR_RNDD),mul(a.l,b.l,MPFR_RNDU)};
    return {rmin(mul(a.l,b.h,MPFR_RNDD),mul(a.h,b.l,MPFR_RNDD)),
            rmax(mul(a.l,b.l,MPFR_RNDU),mul(a.h,b.h,MPFR_RNDU))};
}
inline I inv(const I& a) {
    a.valid();
    if (a.contains_zero()) throw std::domain_error("interval denominator contains zero");
    const R one(1);
    return {div(one, a.h, MPFR_RNDD), div(one, a.l, MPFR_RNDU)};
}
inline I operator/(const I& a, const I& b) { return a * inv(b); }
inline I sq(const I& a) {
    a.valid();
    if (a.l.sign() >= 0) return {square(a.l, MPFR_RNDD), square(a.h, MPFR_RNDU)};
    if (a.h.sign() <= 0) return {square(a.h, MPFR_RNDD), square(a.l, MPFR_RNDU)};
    return {R(0), square(rmax(-a.l,a.h), MPFR_RNDU)};
}
inline I intersect(const I& a, const I& b) { return {rmax(a.l,b.l),rmin(a.h,b.h)}; }
inline I hull(const I& a, const I& b) {
    a.valid(); b.valid(); return {rmin(a.l,b.l),rmax(a.h,b.h)};
}
inline I rt(const I& a) {
    a.valid(); return {root(a.l, MPFR_RNDD),root(a.h, MPFR_RNDU)};
}
inline I lg(const I& a) {
    a.valid(); return {logarithm(a.l, MPFR_RNDD),logarithm(a.h, MPFR_RNDU)};
}
inline I atanfun(const I& a) {
    a.valid(); return {arctangent(a.l, MPFR_RNDD),arctangent(a.h, MPFR_RNDU)};
}
inline I expfun(const I& a) {
    a.valid(); return {exponential(a.l, MPFR_RNDD),exponential(a.h, MPFR_RNDU)};
}
inline I pi() {
    I out;
    mpfr_const_pi(out.l.ptr(), MPFR_RNDD);
    mpfr_const_pi(out.h.ptr(), MPFR_RNDU);
    return out;
}
inline R midpoint(const I& a) {
    a.valid();
    R out = add(a.l,a.h,MPFR_RNDN);
    mpfr_div_2ui(out.ptr(),out.ptr(),1,MPFR_RNDN);
    require_finite(out);
    return rmax(a.l,rmin(a.h,out)); // Chosen point, not an interval bound.
}
inline R width_up(const I& a) { a.valid(); return sub(a.h,a.l,MPFR_RNDU); }

// Derivatives are with respect to the original independent variables.
// The full Hessian array is retained for compatibility. Symmetry avoids
// repeating interval arithmetic for its lower triangle.
template<std::size_t N> struct Jet {
    I v;
    std::array<I,N> d{};
    std::array<std::array<I,N>,N> dd{};
    Jet() = default;
    template<class T, std::enable_if_t<std::is_integral_v<T>, int> = 0>
    Jet(T n) : v(n) {}
    Jet(const R& x) : v(x) {}
    Jet(const I& x) : v(x) {}
    static Jet var(const I& x, std::size_t i) {
        if (i >= N) throw std::out_of_range("jet variable index");
        Jet out(x); out.d[i] = 1; return out;
    }
    friend Jet operator+(const Jet& a, const Jet& b) {
        Jet out(a.v+b.v);
        for (std::size_t i=0;i<N;++i) {
            out.d[i]=a.d[i]+b.d[i];
            for (std::size_t j=i;j<N;++j) {
                out.dd[i][j]=a.dd[i][j]+b.dd[i][j];
                if (i!=j) out.dd[j][i]=out.dd[i][j];
            }
        }
        return out;
    }
    friend Jet operator-(const Jet& a, const Jet& b) {
        Jet out(a.v-b.v);
        for (std::size_t i=0;i<N;++i) {
            out.d[i]=a.d[i]-b.d[i];
            for (std::size_t j=i;j<N;++j) {
                out.dd[i][j]=a.dd[i][j]-b.dd[i][j];
                if (i!=j) out.dd[j][i]=out.dd[i][j];
            }
        }
        return out;
    }
    friend Jet operator-(const Jet& a) {
        Jet out(-a.v);
        for (std::size_t i=0;i<N;++i) {
            out.d[i]=-a.d[i];
            for (std::size_t j=i;j<N;++j) {
                out.dd[i][j]=-a.dd[i][j];
                if (i!=j) out.dd[j][i]=out.dd[i][j];
            }
        }
        return out;
    }
    friend Jet operator*(const Jet& a, const Jet& b) {
        Jet out(a.v*b.v);
        for (std::size_t i=0;i<N;++i) {
            out.d[i]=a.d[i]*b.v+a.v*b.d[i];
            for (std::size_t j=i;j<N;++j) {
                out.dd[i][j]=a.dd[i][j]*b.v+a.d[i]*b.d[j]
                            +a.d[j]*b.d[i]+a.v*b.dd[i][j];
                if (i!=j) out.dd[j][i]=out.dd[i][j];
            }
        }
        return out;
    }
    friend Jet operator/(const Jet& a, const Jet& b) {
        return a*compose(b,inv(b.v),-inv(sq(b.v)),2/(sq(b.v)*b.v));
    }
    static Jet compose(const Jet& a, const I& value, const I& deriv, const I& deriv2) {
        Jet out(value);
        for (std::size_t i=0;i<N;++i) {
            out.d[i]=deriv*a.d[i];
            for (std::size_t j=i;j<N;++j) {
                out.dd[i][j]=deriv2*a.d[i]*a.d[j]+deriv*a.dd[i][j];
                if (i!=j) out.dd[j][i]=out.dd[i][j];
            }
        }
        return out;
    }
};

template<std::size_t N>
inline Jet<N> fun(const Jet<N>& a, const I& v, const I& d, const I& dd) {
    return Jet<N>::compose(a,v,d,dd);
}
template<std::size_t N> inline Jet<N> inv(const Jet<N>& a) {
    return fun(a,inv(a.v),-inv(sq(a.v)),2/(sq(a.v)*a.v));
}
template<std::size_t N> inline Jet<N> sq(const Jet<N>& a) {
    return fun(a,sq(a.v),2*a.v,2);
}
template<std::size_t N> inline Jet<N> lg(const Jet<N>& a) {
    return fun(a,lg(a.v),inv(a.v),-inv(sq(a.v)));
}
template<std::size_t N> inline Jet<N> rt(const Jet<N>& a) {
    if (a.v.l.sign() <= 0) throw std::domain_error("sqrt jet requires a positive box");
    I v=rt(a.v); return fun(a,v,inv(2*v),-inv(4*a.v*v));
}
template<std::size_t N> inline Jet<N> atanfun(const Jet<N>& a) {
    return fun(a,atanfun(a.v),inv(1+sq(a.v)),-2*a.v/sq(1+sq(a.v)));
}
template<std::size_t N> inline Jet<N> expfun(const Jet<N>& a) {
    I v=expfun(a.v); return fun(a,v,v,v);
}

// The analytic continuation of log(h)/(h-1), including h=1. With
// t=(h-1)/(h+1), this is (1-t)*sum_{n>=0} t^(2n)/(2n+1).
// The omitted tail and its first two derivatives are bounded by
// derivatives of t^(2M+2)/((2M+3)*(1-t^2)) at |t|<=tau<1.
// This follows coefficient by coefficient; differentiating a numerical
// approximation and treating it as the true derivative would be invalid.
template<std::size_t N>
inline Jet<N> logdiv(const Jet<N>& h, unsigned M=16) {
    if(h.v.l.sign()<=0 || M>1000)
        throw std::domain_error("logdiv requires h>0 and a bounded series order");
    const I low=(I(h.v.l)-1)/(I(h.v.l)+1);
    const I high=(I(h.v.h)-1)/(I(h.v.h)+1);
    const I den=h.v+1;
    const Jet<N> t=fun(h,I(low.l,high.h),2/sq(den),-4/(sq(den)*den));
    const R tau=rmax(abs(t.v.l),abs(t.v.h));
    if(tau>=R(1)) throw std::domain_error("logdiv transformed interval reaches one");
    using U=Jet<1>;
    U x=U::var(t.v,0), x2=sq(x), power=1, sum=1;
    for(unsigned n=1;n<=M;++n) {
        power=power*x2;
        sum=sum+U(I::rational(1,2*n+1))*power;
    }
    U y=U::var(I(R(0),tau),0), y2=sq(y), tail_power=1;
    for(unsigned n=0;n<=M;++n) tail_power=tail_power*y2;
    U tail=tail_power/(U(2*M+3)*(1-y2));
    const I value=sum.v+I(R(0),tail.v.h);
    const I deriv=sum.d[0]+I(-tail.d[0].h,tail.d[0].h);
    const I deriv2=sum.dd[0][0]+I(R(0),tail.dd[0][0].h);
    return (1-t)*fun(t,value,deriv,deriv2);
}

template<std::size_t N>
inline std::array<R,N> centers(const std::array<I,N>& box) {
    std::array<R,N> out;
    for(std::size_t i=0;i<N;++i) out[i]=midpoint(box[i]);
    return out;
}
template<std::size_t N>
inline std::array<Jet<N>,N> variables(const std::array<I,N>& box) {
    std::array<Jet<N>,N> out;
    for(std::size_t i=0;i<N;++i) out[i]=Jet<N>::var(box[i],i);
    return out;
}
template<std::size_t N>
inline std::array<Jet<N>,N> variables_at(const std::array<R,N>& center) {
    std::array<Jet<N>,N> out;
    for(std::size_t i=0;i<N;++i) out[i]=Jet<N>::var(I(center[i]),i);
    return out;
}
// "at" must be evaluated at this exact center, and "all" on the box.
// The line segment from center to every box point stays in the box.
template<std::size_t N>
inline I taylor(const Jet<N>& at, const Jet<N>& all,
                const std::array<I,N>& box, const std::array<R,N>& center) {
    std::array<I,N> dx;
    for(std::size_t i=0;i<N;++i) {
        box[i].valid();
        if(center[i]<box[i].l || center[i]>box[i].h)
            throw std::domain_error("Taylor center outside its box");
        dx[i]=box[i]-I(center[i]);
    }
    I out=at.v;
    for(std::size_t i=0;i<N;++i) {
        out=out+at.d[i]*dx[i]+all.dd[i][i]*sq(dx[i])/2;
        for(std::size_t j=i+1;j<N;++j)
            out=out+all.dd[i][j]*dx[i]*dx[j];
    }
    I result=intersect(out,all.v);
    result.valid();
    return result;
}

// Call before a run; do not change the MPFR exponent range or clear flags
// during a certified evaluation. Inexact is normal; range/domain flags fail.
inline void check_environment() {
    if (std::strcmp(mpfr_get_version(),MPFR_VERSION_STRING)!=0)
        throw std::runtime_error("MPFR header/runtime version mismatch");
    if (mpfr_custom_get_size(precision) >
        ((precision+GMP_NUMB_BITS-1)/GMP_NUMB_BITS)*sizeof(mp_limb_t))
        throw std::runtime_error("insufficient MPFR custom storage");
    if (mp_bits_per_limb != GMP_NUMB_BITS)
        throw std::runtime_error("GMP limb ABI mismatch");
    mpfr_clear_flags();
}
inline void check_flags() {
    constexpr mpfr_flags_t bad=MPFR_FLAGS_UNDERFLOW|MPFR_FLAGS_OVERFLOW
        |MPFR_FLAGS_NAN|MPFR_FLAGS_DIVBY0|MPFR_FLAGS_ERANGE;
    if (mpfr_flags_test(bad))
        throw std::runtime_error("MPFR range/domain exception during certificate");
}

} // namespace certified
#endif
