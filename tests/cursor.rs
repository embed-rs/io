extern crate io;
use io::prelude::*;

#[test]
fn sanity() {
    let mut rdr = io::Cursor::<_, io::Void>::new([2, 5, 3, 0]);
    let mut buf = [0; 2];
    rdr.read(&mut buf).unwrap();
    assert_eq!(buf, [2, 5]);
}
