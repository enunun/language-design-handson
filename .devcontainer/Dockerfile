# miseの公式Debianイメージ．git，curl，CA証明書とmiseを含み，
# PATHに/mise/shims，MISE_DATA_DIRに/miseが設定済み．
FROM jdxcode/mise:2026.9.12-debian

RUN apt-get update \
	&& apt-get install -y --no-install-recommends \
	openssh-client \
	procps \
	jq \
	libatomic1 \
	&& rm -rf /var/lib/apt/lists/*

# 証明支援系Lean 4を，版管理ツールelanで入れる．
# 使うLeanの版はリポジトリのlean-toolchainで固定し，イメージの作成時に取得しておく．
ENV ELAN_HOME=/opt/elan \
	PATH=/opt/elan/bin:$PATH
COPY lean-toolchain /tmp/lean-toolchain
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh \
	&& sh /tmp/elan-init.sh -y --no-modify-path --default-toolchain "$(cat /tmp/lean-toolchain)" \
	&& rm /tmp/elan-init.sh /tmp/lean-toolchain \
	&& lean --version

# ツール(rtk，lefthookなど)はmise.tomlとmise.lockのとおりにイメージへ入れる．
# --lockedにより，mise.lockにない版やチェックサムの合わないファイルは入れない．
WORKDIR /tmp/mise-bootstrap
COPY mise.toml mise.lock ./
RUN mise trust \
	&& mise ls --current \
	&& mise install --locked --verbose

# rtkのhookを有効化する．
RUN mkdir -p /root/.claude \
	&& rtk init -g --hook-only

# 起動後は，リポジトリのmise.tomlをグローバル設定として読む．
# これにより，/workspacesの外のディレクトリでも同じツールを使える．
# グローバル設定のルートも/workspacesにして，タスクをリポジトリ直下で実行させる
# (未指定だとホームディレクトリで実行される)．
ENV MISE_GLOBAL_CONFIG_FILE=/workspaces/mise.toml \
	MISE_GLOBAL_CONFIG_ROOT=/workspaces \
	MISE_TRUSTED_CONFIG_PATHS=/workspaces

WORKDIR /workspaces
