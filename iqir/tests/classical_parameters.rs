use iqir::frontend;

fn parse(body: &str) -> Result<iqir::Program, String> {
    frontend::parse_str_with_options(
        &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
        "calls.qasm",
        true,
    )
    .map_err(|e| e.to_string())
}

#[test]
fn numeric_bit_and_quantum_parameters_and_returns_have_dense_ids() {
    for source in [
        "def inc(int[8] value)->int[8]{value+=1; return value;} int[8] a=2; int[8] result=inc(a); result=inc(result);",
        "def f(float[32] theta, qubit q)->float[32]{ry(theta) q; theta+=1.0; return theta;} qubit q; float[32] result=f(0.0,q);",
        "def flip(bool flag, bit[2] bits)->bool{flag=!flag; bits[0]=false; return flag;} bool result=flip(true,\"11\");",
        "def positive(int[32] value)->bool{return value>0;} qubit q; if(positive(1)){x q;}",
        "def inner(int[8] value)->int[8]{return value;} def outer(int[8] value)->int[8]{return inner(value);} int[8] result=outer(2);",
        "def gcd(int[32] a,int[32] b)->int[32]{while(b!=0){int[32] rem=a%b; a=b; b=rem;} return a;} int[32] result=gcd(12,8);",
        "def f(int[32] count,qubit q){for int i in [0:count]{x q;}} qubit q; f(2,q);",
        "def f(int[32] count,qubit q){while(count>0){for int i in [0:count]{x q;} count-=1;}} qubit q; f(2,q);",
    ] {
        let p = parse(source).unwrap();
        let mut ids = vec![];
        p.visit_ast_ids(|id| ids.push(id.index()));
        ids.sort();
        assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>(), "{source}");
    }
}

#[test]
fn invalid_calls_do_not_leak_scopes_aliases_or_const_facts() {
    for source in [
        "def f(int[8] value,int[8] value){}",
        "def f(int[8] value){} f();",
        "def f(int[8] value){} f(1,2);",
        "def f(int[8] value){} float[64] a=1.0; f(a);",
        "def f(int[8] value){} int[16] a=1; f(a);",
        "def f(int[8] value){} qubit q; f(q);",
        "def f(qubit a,qubit b,int[8] n){} qubit q; f(q,q,1);",
        "def f(int[8] value)->int[8]{return value;} bool result=f(1);",
        "def f(int[8] value)->int[8]{return value;} int[16] result=f(1);",
        "def f(int[8] value)->int[8]{return value;} const int[8] result=f(1);",
        "def f(int[8] value){const int[8] c=value;} f(1);",
        "def f(int[8] value)->int[8]{f(value);return value;} int[8] result=f(1);",
        "int[8] global=0; def f(int[8] value)->int[8]{return global;} int[8] result=f(1);",
        "def f(int[8] value)->int[8]{return later;} const int[8] later=1; int[8] result=f(1);",
        "def f(int[8] value)->int[8]{return hidden;} def g(int[8] hidden)->int[8]{return f(hidden);} int[8] result=g(1);",
        "def f(int[8] value)->int[8]{if(value>0){return value;} return 0;} int[8] result=f(1);",
        "def f(int[8] value)->bool{return value>0;} while(f(1)){}",
        "def f(int[8] value)->bool{return value>0;} qubit q; if(false && f(1)){x q;}",
    ] {
        assert!(parse(source).is_err(), "unexpected success: {source}");
    }
}
