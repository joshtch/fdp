// This has to be a babel.config.js and not .babelrc or in package.json so
// Jest will correctly use it to transpile fd-related node modules
const { BABEL_ENV } = process.env;

module.exports = {
  presets: [
    [
      '@babel/env',
      {
        targets: {
          browsers: ['ie >= 11'],
        },
        exclude: ['transform-async-to-generator', 'transform-regenerator'],
        modules: BABEL_ENV === 'commonjs' ? 'cjs' : false,
        loose: true,
      },
    ],
  ],
  plugins: [
    // don't use `loose` mode here - need to copy symbols when spreading
    '@babel/proposal-object-rest-spread',
  ],
  env: {
    test: {
      plugins: ['@babel/transform-modules-commonjs'],
    },
  },
};
