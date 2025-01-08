package clienttest

import (
	"context"
	"os"
	"strings"
	"testing"

	"deps.dev/util/resolve"
	"deps.dev/util/resolve/schema"
	"github.com/google/osv-scalibr/extractor"
	"github.com/google/osv-scanner/internal/imodels"
	"github.com/google/osv-scanner/internal/resolution/client"
	"github.com/google/osv-scanner/internal/utility/vulns"
	"github.com/google/osv-scanner/pkg/lockfile"
	"github.com/google/osv-scanner/pkg/models"
	"gopkg.in/yaml.v3"
)

type ResolutionUniverse struct {
	System string                 `yaml:"system"`
	Schema string                 `yaml:"schema"`
	Vulns  []models.Vulnerability `yaml:"vulns"`
}

type mockVulnerabilityMatcher []models.Vulnerability

func (mvc mockVulnerabilityMatcher) MatchVulnerabilities(_ context.Context, invs []*extractor.Inventory) ([][]*models.Vulnerability, error) {
	result := make([][]*models.Vulnerability, len(invs))
	for i, inv := range invs {
		pkg := imodels.FromInventory(inv)
		// TODO (V2 Models): remove this once PackageDetails has been migrated
		mappedPackageDetails := lockfile.PackageDetails{
			Name:      pkg.Name(),
			Version:   pkg.Version(),
			Commit:    pkg.Commit(),
			Ecosystem: lockfile.Ecosystem(pkg.Ecosystem().String()),
			CompareAs: lockfile.Ecosystem(pkg.Ecosystem().String()),
			DepGroups: pkg.DepGroups(),
		}
		for _, v := range mvc {
			if vulns.IsAffected(v, mappedPackageDetails) {
				result[i] = append(result[i], &v)
			}
		}
	}

	return result, nil
}

type mockDependencyClient struct {
	*resolve.LocalClient
}

func (mdc mockDependencyClient) LoadCache(string) error                  { return nil }
func (mdc mockDependencyClient) WriteCache(string) error                 { return nil }
func (mdc mockDependencyClient) AddRegistries(_ []client.Registry) error { return nil }

func NewMockResolutionClient(t *testing.T, universeYAML string) client.ResolutionClient {
	t.Helper()
	f, err := os.Open(universeYAML)
	if err != nil {
		t.Fatalf("failed opening mock universe: %v", err)
	}
	defer f.Close()
	dec := yaml.NewDecoder(f)

	var universe ResolutionUniverse
	if err := dec.Decode(&universe); err != nil {
		t.Fatalf("failed decoding mock universe: %v", err)
	}

	cl := client.ResolutionClient{
		VulnerabilityMatcher: mockVulnerabilityMatcher(universe.Vulns),
	}

	var sys resolve.System
	switch strings.ToLower(universe.System) {
	case "npm":
		sys = resolve.NPM
	case "maven":
		sys = resolve.Maven
	default:
		t.Fatalf("unknown ecosystem in universe: %s", universe.System)
	}

	// schema needs a strict tab indentation, which is awkward to do within the YAML.
	// Replace double space from yaml with single tab
	universe.Schema = strings.ReplaceAll(universe.Schema, "  ", "\t")
	sch, err := schema.New(universe.Schema, sys)
	if err != nil {
		t.Fatalf("failed parsing schema: %v", err)
	}

	cl.DependencyClient = mockDependencyClient{sch.NewClient()}

	return cl
}
