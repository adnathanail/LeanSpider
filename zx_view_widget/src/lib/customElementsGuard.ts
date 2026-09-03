/**
 * Make re-registering zxcc's web components a no-op.
 *
 * The InfoView re-evaluates this bundle whenever the panel restarts, inside a
 * page that has already run it once. zxcc registers its elements (`zx-diagram`,
 * `zx-viewer`, …) with lit's `@customElement`, i.e. a bare `customElements
 * .define` at module-eval time, so the second evaluation throws
 *
 *   Failed to execute 'define' on 'CustomElementRegistry':
 *   the name "zx-viewer" has already been used with this registry
 *
 * and nothing renders until the whole window is reloaded.
 *
 * Skipping the redefinition leaves the classes from the *first* evaluation
 * registered, and that is what a freshly created `<zx-diagram>` tag upgrades to.
 * So a change to the widget's own code shows up on an InfoView restart, but a
 * change to zxcc still needs a window reload to take effect.
 *
 * Only `zx-` names are guarded, so a genuine duplicate registration from some
 * other widget sharing the page still raises.
 *
 * Import this for its side effect, and *before* zxcc, so the patch is in place
 * by the time lit's decorators run.
 */

declare global {
  interface CustomElementRegistry {
    /** Set by this module so a re-evaluation doesn't wrap `define` twice. */
    __zxDefineGuarded?: boolean
  }
}

const registry = window.customElements

if (!registry.__zxDefineGuarded) {
  registry.__zxDefineGuarded = true
  const define = registry.define.bind(registry)
  registry.define = (name, ctor, options) => {
    if (name.startsWith('zx-') && registry.get(name)) return
    define(name, ctor, options)
  }
}

export {}
