// SPDX-License-Identifier: PMPL-1.0-or-later
// FFI Integration Test - Tests that all 3 interfaces can use the FFI layer

#[cfg(test)]
mod tests {
    use std::process::Command;
    use std::time::Duration;
    use tokio::time::sleep;

    #[tokio::test]
    async fn test_ffi_initialization() {
        // Test that the FFI layer can be initialized
        let output = Command::new("cargo")
            .args(["test", "--lib", "ffi"])
            .current_dir("../..")
            .output()
            .expect("Failed to run FFI tests");

        assert!(output.status.success(), "FFI tests failed: {}", String::from_utf8_lossy(&output.stderr));
    }

    #[tokio::test]
    async fn test_graphql_ffi_integration() {
        // This would test the GraphQL interface with FFI
        // For now, just verify it compiles
        let output = Command::new("cargo")
            .args(["check", "--package", "echidna-graphql"])
            .current_dir("../..")
            .output()
            .expect("Failed to check GraphQL package");

        assert!(output.status.success(), "GraphQL check failed: {}", String::from_utf8_lossy(&output.stderr));
    }

    #[tokio::test]
    async fn test_grpc_ffi_integration() {
        // This would test the gRPC interface with FFI
        // For now, just verify it compiles
        let output = Command::new("cargo")
            .args(["check", "--package", "echidna-grpc"])
            .current_dir("../..")
            .output()
            .expect("Failed to check gRPC package");

        assert!(output.status.success(), "gRPC check failed: {}", String::from_utf8_lossy(&output.stderr));
    }

    #[tokio::test]
    async fn test_rest_ffi_integration() {
        // This would test the REST interface with FFI
        // For now, just verify it compiles
        let output = Command::new("cargo")
            .args(["check", "--package", "echidna-rest"])
            .current_dir("../..")
            .output()
            .expect("Failed to check REST package");

        assert!(output.status.success(), "REST check failed: {}", String::from_utf8_lossy(&output.stderr));
    }

    #[tokio::test]
    async fn test_all_interfaces_compile() {
        // Test that all interfaces compile with FFI support
        let output = Command::new("cargo")
            .args(["check", "--workspace"])
            .current_dir("../..")
            .output()
            .expect("Failed to check workspace");

        assert!(output.status.success(), "Workspace check failed: {}", String::from_utf8_lossy(&output.stderr));
    }
}
