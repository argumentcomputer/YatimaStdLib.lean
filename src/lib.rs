use blake3::hash;

#[no_mangle]
extern "C" fn blake3(mem: &mut [u8; 32], input: &[u8]) {
    let x = hash(input);
    // *mem = *hash(input).as_bytes();
}
