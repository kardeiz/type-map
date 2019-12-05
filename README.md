# extensions

[![Docs](https://docs.rs/extensions/badge.svg)](https://docs.rs/crate/extensions/)
[![Crates.io](https://img.shields.io/crates/v/extensions.svg)](https://crates.io/crates/extensions)

`Extensions` is a `typemap` for `Any` values, similar to [`typemap`](https://github.com/reem/rust-typemap),
[`http::Extensions`](https://docs.rs/http/*/http/struct.Extensions.html), and [`actix-http::Extensions`](https://docs.rs/actix-http/*/actix_http/struct.Extensions.html).

Provides the best of both `http::Extensions` and `actix_http::Extensions`, with some code and tests drawn directly from `actix-http::Extensions`.

Useful when you need a typemap container, but not in the context of `actix-web` or an `http` project.