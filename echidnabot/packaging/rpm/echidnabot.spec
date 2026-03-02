# RPM spec file for echidnabot
# Compatible with Fedora (dnf) and openSUSE (zypper)

Name:           echidnabot
Version:        0.1.0
Release:        1%{?dist}
Summary:        Proof-aware CI bot for theorem proof verification

License:        PMPL-1.0-or-later
URL:            https://github.com/hyperpolymath/echidnabot
Source0:        %{name}-%{version}.tar.gz

BuildRequires:  rust >= 1.70
BuildRequires:  cargo
BuildRequires:  gcc
BuildRequires:  pkg-config
BuildRequires:  openssl-devel

Requires:       openssl

%description
ECHIDNABOT is a proof-aware CI bot that orchestrates ECHIDNA for theorem
proof verification. It integrates with GitHub to automatically verify
formal proofs in pull requests.

Features:
- GitHub webhook integration for automated PR verification
- GraphQL API for proof status queries
- Support for multiple theorem provers via ECHIDNA
- PostgreSQL and SQLite database backends
- Real-time proof status updates

%prep
%autosetup

%build
cargo build --release

%check
cargo test --release

%install
install -D -m 755 target/release/echidnabot %{buildroot}%{_bindir}/echidnabot

# Systemd service
install -D -m 644 /dev/stdin %{buildroot}%{_unitdir}/echidnabot.service <<EOF
[Unit]
Description=ECHIDNA Proof Verification CI Bot
After=network.target

[Service]
Type=simple
User=echidnabot
ExecStart=%{_bindir}/echidnabot serve
Restart=on-failure
Environment=ECHIDNABOT_CONFIG=/etc/echidnabot/config.toml

[Install]
WantedBy=multi-user.target
EOF

%files
%license LICENSE
%doc README.adoc
%{_bindir}/echidnabot
%{_unitdir}/echidnabot.service

%post
%systemd_post echidnabot.service

%preun
%systemd_preun echidnabot.service

%postun
%systemd_postun_with_restart echidnabot.service

%changelog
* Tue Dec 17 2025 hyperpolymath <packages@hyperpolymath.dev> - 0.1.0-1
- Initial release
