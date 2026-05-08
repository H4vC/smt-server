use smt_wire::{Client, Context, Op, Status, Term};

fn status_name(status: Status) -> &'static str {
    match status {
        Status::Simplified => "Status::Simplified",
        Status::Sat => "Status::Sat",
        Status::Unsat => "Status::Unsat",
        Status::Unknown => "Status::Unknown",
        Status::Error => "Status::Error",
    }
}

fn to_rpn(term: &Term, mut args: Vec<String>) -> smt_wire::Result<String> {
    match term.op()? {
        Op::BvVar => term.name(),
        Op::BvConst => {
            if let Term::Bv(bv) = term {
                Ok(format!("{}:{}", term.value_u128()?, bv.width()?))
            } else {
                unreachable!("BV_CONST is a BV term")
            }
        }
        op => {
            args.push(op.smt_symbol().to_owned());
            Ok(args.join(" "))
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let ctx = Context::new();
    println!("{ctx}"); // Context#1, Context#2, ...

    let x = ctx.bv_var("x", 32)?;
    let y = ctx.bv_var("y", 32)?;

    // Rust does not overload SMT operators; use Context methods instead.
    // Integer operands are coerced to BV constants using the left term's width.
    let x_plus_y = ctx.bv_add(&x, &y)?;
    let x_xor_y = ctx.bv_xor(&x, &y)?;
    let x_and_y = ctx.bv_and(&x, &y)?;
    let mba = ctx.bv_add(&x_xor_y, ctx.bv_mul(&x_and_y, 2u64)?)?;
    let masked = ctx.bv_and(&ctx.bv_add(&x, 3u64)?, 0xffu64)?;

    // Named operations live on Context: comparisons, structural operations, and Bool ops.
    let identity_holds = ctx.bv_eq(&mba, &x_plus_y)?;
    let low_x = ctx.bv_extract(&x, 7, 0)?;
    let low_x_is_42 = ctx.bv_eq(&low_x, 42u64)?;
    let assertion = ctx.bool_and(&identity_holds, &low_x_is_42)?;
    ctx.assert_(&assertion)?;

    println!("MBA: {}", mba.to_smt2(0)?);
    println!("MBA full: {}", mba.to_smt2(-1)?);
    println!("masked: {}", masked.to_smt2(-1)?);

    let mut lower = to_rpn;
    println!("RPN: {}", mba.as_term().visit(&mut lower)?);

    // Start the server first:
    //   cargo run -p smt-server -- 127.0.0.1:9123
    // Or set SMT_SERVER_ADDRESS=<host>:<port> to choose a different default.
    let mut client = Client::connect_default()?;
    let resp = client.solve(&ctx)?;
    println!("{}", status_name(resp.status));
    if resp.status == Status::Sat {
        if let Some(model) = &resp.model {
            let mut items = model
                .iter()
                .map(|(var, value)| Ok((var.name()?, value.as_u128()?)))
                .collect::<smt_wire::Result<Vec<_>>>()?;
            items.sort_by(|a, b| a.0.cmp(&b.0));
            for (name, value) in items {
                println!("{name} = 0x{value:x}");
            }
        }
    }

    let simplified = client.simplify(&mba.as_term())?;
    if let Some(term) = simplified.term {
        println!("simplified MBA: {}", term.to_smt2(-1)?);
    }

    println!("\nSMT-LIB:");
    let ctx_smt2 = ctx.to_smt2()?;
    println!("{ctx_smt2}");

    let smt_resp = client.smt2(&ctx_smt2)?;
    println!("{smt_resp}");

    Ok(())
}
