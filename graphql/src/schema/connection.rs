pub fn is_connection_type(field_or_type_name: &str) -> bool {
    // the field return type will have *Connection
    // or the field name will be *Paginated
    field_or_type_name.ends_with("Connection") || field_or_type_name.ends_with("Paginated")
}

#[test]
fn test_is_valid_connection_type() {
    assert!(is_connection_type("FooConnection"));
    assert!(is_connection_type("barPaginated"));
    assert!(!is_connection_type("Foo"));
}
